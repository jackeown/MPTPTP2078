%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:48 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 474 expanded)
%              Number of clauses        :   88 ( 102 expanded)
%              Number of leaves         :   20 ( 210 expanded)
%              Depth                    :   19
%              Number of atoms          :  718 (6336 expanded)
%              Number of equality atoms :  185 ( 647 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),sK6) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK6)
        & r2_hidden(sK6,u1_struct_0(X2))
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
              & r2_hidden(X5,u1_struct_0(X2))
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK5),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X5)
            & r2_hidden(X5,u1_struct_0(X2))
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                  & r2_hidden(X5,u1_struct_0(X2))
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k3_tmap_1(X0,X1,sK4,X2,X4),X5) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X5)
                & r2_hidden(X5,u1_struct_0(X2))
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                      & r2_hidden(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,u1_struct_0(X3)) )
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
                    ( k1_funct_1(k3_tmap_1(X0,X1,X3,sK3,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                    & r2_hidden(X5,u1_struct_0(sK3))
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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
                        ( k1_funct_1(k3_tmap_1(X0,sK2,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X5)
                        & r2_hidden(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,u1_struct_0(X3)) )
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

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                            & r2_hidden(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,u1_struct_0(X3)) )
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
                          ( k1_funct_1(k3_tmap_1(sK1,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
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

fof(f38,plain,
    ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6)
    & r2_hidden(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f25,f37,f36,f35,f34,f33,f32])).

fof(f58,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    r2_hidden(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1718,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2379,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1718])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_494,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_495,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(sK5)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_499,plain,
    ( ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_18])).

cnf(c_500,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_1707,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X3_56))))
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ v2_pre_topc(X2_56)
    | ~ v2_pre_topc(X3_56)
    | ~ l1_pre_topc(X2_56)
    | ~ l1_pre_topc(X3_56)
    | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X3_56),sK5,u1_struct_0(X0_56)) = k3_tmap_1(X2_56,X3_56,X1_56,X0_56,sK5)
    | u1_struct_0(X1_56) != u1_struct_0(sK4)
    | u1_struct_0(X3_56) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_2390,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK5,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,sK5)
    | u1_struct_0(X0_56) != u1_struct_0(sK4)
    | u1_struct_0(X1_56) != u1_struct_0(sK2)
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X3_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1707])).

cnf(c_3348,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0_56),sK5,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,X0_56,sK4,X1_56,sK5)
    | u1_struct_0(X0_56) != u1_struct_0(sK2)
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X2_56) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2390])).

cnf(c_3596,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_56)) = k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5)
    | m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X0_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X1_56) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3348])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1721,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2376,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_576,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_1704,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
    inference(subtyping,[status(esa)],[c_576])).

cnf(c_2393,plain,
    ( k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1704])).

cnf(c_2872,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(superposition,[status(thm)],[c_2376,c_2393])).

cnf(c_3597,plain,
    ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3596,c_2872])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3645,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_32,c_33,c_34,c_41])).

cnf(c_3646,plain,
    ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,sK4) != iProver_top
    | m1_pre_topc(sK4,X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_3645])).

cnf(c_3660,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3))
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_3646])).

cnf(c_1739,plain,
    ( k1_funct_1(X0_54,X1_54) = k1_funct_1(X2_54,X3_54)
    | X0_54 != X2_54
    | X1_54 != X3_54 ),
    theory(equality)).

cnf(c_3298,plain,
    ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6)
    | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k7_relat_1(sK5,u1_struct_0(sK3))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_1734,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_2599,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != X0_55
    | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != X0_55
    | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_3284,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6)
    | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6)
    | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_2651,plain,
    ( X0_55 != X1_55
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != X1_55
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = X0_55 ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_2901,plain,
    ( X0_55 != k1_funct_1(sK5,sK6)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = X0_55
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_3138,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != k1_funct_1(sK5,sK6)
    | k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) != k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_2901])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK2) != X3
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_18,c_16])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK5,X0_54) ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_2795,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = k1_funct_1(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_196,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_254,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_196])).

cnf(c_1710,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_254])).

cnf(c_2639,plain,
    ( ~ r1_tarski(X0_54,u1_struct_0(sK4))
    | v1_xboole_0(X0_54)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1710])).

cnf(c_2722,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2639])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1726,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | ~ m1_pre_topc(X2_56,X0_56)
    | r1_tarski(u1_struct_0(X2_56),u1_struct_0(X0_56))
    | ~ v2_pre_topc(X1_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2630,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X1_56,sK1)
    | ~ m1_pre_topc(X0_56,sK1)
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_2690,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_pre_topc(sK4,sK1)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_1731,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2660,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2588,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_402,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | u1_struct_0(sK3) != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_403,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK3)),sK6) = k1_funct_1(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_550,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK3)),sK6) = k1_funct_1(X0,sK6)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_403,c_18])).

cnf(c_551,plain,
    ( ~ v1_relat_1(sK5)
    | k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) = k1_funct_1(sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_1706,plain,
    ( ~ v1_relat_1(sK5)
    | k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) = k1_funct_1(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_551])).

cnf(c_12,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1724,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_417,plain,
    ( ~ v1_xboole_0(X0)
    | u1_struct_0(sK3) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_418,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3660,c_3298,c_3284,c_3138,c_2795,c_2722,c_2690,c_2660,c_2588,c_1706,c_1724,c_418,c_14,c_42,c_15,c_16,c_38,c_19,c_21,c_31,c_26,c_30,c_27,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:27:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.82/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.82/0.98  
% 1.82/0.98  ------  iProver source info
% 1.82/0.98  
% 1.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.82/0.98  git: non_committed_changes: false
% 1.82/0.98  git: last_make_outside_of_git: false
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing Options
% 1.82/0.98  
% 1.82/0.98  --preprocessing_flag                    true
% 1.82/0.98  --time_out_prep_mult                    0.1
% 1.82/0.98  --splitting_mode                        input
% 1.82/0.98  --splitting_grd                         true
% 1.82/0.98  --splitting_cvd                         false
% 1.82/0.98  --splitting_cvd_svl                     false
% 1.82/0.98  --splitting_nvd                         32
% 1.82/0.98  --sub_typing                            true
% 1.82/0.98  --prep_gs_sim                           true
% 1.82/0.98  --prep_unflatten                        true
% 1.82/0.98  --prep_res_sim                          true
% 1.82/0.98  --prep_upred                            true
% 1.82/0.98  --prep_sem_filter                       exhaustive
% 1.82/0.98  --prep_sem_filter_out                   false
% 1.82/0.98  --pred_elim                             true
% 1.82/0.98  --res_sim_input                         true
% 1.82/0.98  --eq_ax_congr_red                       true
% 1.82/0.98  --pure_diseq_elim                       true
% 1.82/0.98  --brand_transform                       false
% 1.82/0.98  --non_eq_to_eq                          false
% 1.82/0.98  --prep_def_merge                        true
% 1.82/0.98  --prep_def_merge_prop_impl              false
% 1.82/0.98  --prep_def_merge_mbd                    true
% 1.82/0.98  --prep_def_merge_tr_red                 false
% 1.82/0.98  --prep_def_merge_tr_cl                  false
% 1.82/0.98  --smt_preprocessing                     true
% 1.82/0.98  --smt_ac_axioms                         fast
% 1.82/0.98  --preprocessed_out                      false
% 1.82/0.98  --preprocessed_stats                    false
% 1.82/0.98  
% 1.82/0.98  ------ Abstraction refinement Options
% 1.82/0.98  
% 1.82/0.98  --abstr_ref                             []
% 1.82/0.98  --abstr_ref_prep                        false
% 1.82/0.98  --abstr_ref_until_sat                   false
% 1.82/0.98  --abstr_ref_sig_restrict                funpre
% 1.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.98  --abstr_ref_under                       []
% 1.82/0.98  
% 1.82/0.98  ------ SAT Options
% 1.82/0.98  
% 1.82/0.98  --sat_mode                              false
% 1.82/0.98  --sat_fm_restart_options                ""
% 1.82/0.98  --sat_gr_def                            false
% 1.82/0.98  --sat_epr_types                         true
% 1.82/0.98  --sat_non_cyclic_types                  false
% 1.82/0.98  --sat_finite_models                     false
% 1.82/0.98  --sat_fm_lemmas                         false
% 1.82/0.98  --sat_fm_prep                           false
% 1.82/0.98  --sat_fm_uc_incr                        true
% 1.82/0.98  --sat_out_model                         small
% 1.82/0.98  --sat_out_clauses                       false
% 1.82/0.98  
% 1.82/0.98  ------ QBF Options
% 1.82/0.98  
% 1.82/0.98  --qbf_mode                              false
% 1.82/0.98  --qbf_elim_univ                         false
% 1.82/0.98  --qbf_dom_inst                          none
% 1.82/0.98  --qbf_dom_pre_inst                      false
% 1.82/0.98  --qbf_sk_in                             false
% 1.82/0.98  --qbf_pred_elim                         true
% 1.82/0.98  --qbf_split                             512
% 1.82/0.98  
% 1.82/0.98  ------ BMC1 Options
% 1.82/0.98  
% 1.82/0.98  --bmc1_incremental                      false
% 1.82/0.98  --bmc1_axioms                           reachable_all
% 1.82/0.98  --bmc1_min_bound                        0
% 1.82/0.98  --bmc1_max_bound                        -1
% 1.82/0.98  --bmc1_max_bound_default                -1
% 1.82/0.98  --bmc1_symbol_reachability              true
% 1.82/0.98  --bmc1_property_lemmas                  false
% 1.82/0.98  --bmc1_k_induction                      false
% 1.82/0.98  --bmc1_non_equiv_states                 false
% 1.82/0.98  --bmc1_deadlock                         false
% 1.82/0.98  --bmc1_ucm                              false
% 1.82/0.98  --bmc1_add_unsat_core                   none
% 1.82/0.98  --bmc1_unsat_core_children              false
% 1.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.98  --bmc1_out_stat                         full
% 1.82/0.98  --bmc1_ground_init                      false
% 1.82/0.98  --bmc1_pre_inst_next_state              false
% 1.82/0.98  --bmc1_pre_inst_state                   false
% 1.82/0.98  --bmc1_pre_inst_reach_state             false
% 1.82/0.98  --bmc1_out_unsat_core                   false
% 1.82/0.98  --bmc1_aig_witness_out                  false
% 1.82/0.98  --bmc1_verbose                          false
% 1.82/0.98  --bmc1_dump_clauses_tptp                false
% 1.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.98  --bmc1_dump_file                        -
% 1.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.98  --bmc1_ucm_extend_mode                  1
% 1.82/0.98  --bmc1_ucm_init_mode                    2
% 1.82/0.98  --bmc1_ucm_cone_mode                    none
% 1.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.98  --bmc1_ucm_relax_model                  4
% 1.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.98  --bmc1_ucm_layered_model                none
% 1.82/0.98  --bmc1_ucm_max_lemma_size               10
% 1.82/0.98  
% 1.82/0.98  ------ AIG Options
% 1.82/0.98  
% 1.82/0.98  --aig_mode                              false
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation Options
% 1.82/0.98  
% 1.82/0.98  --instantiation_flag                    true
% 1.82/0.98  --inst_sos_flag                         false
% 1.82/0.98  --inst_sos_phase                        true
% 1.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel_side                     num_symb
% 1.82/0.98  --inst_solver_per_active                1400
% 1.82/0.98  --inst_solver_calls_frac                1.
% 1.82/0.98  --inst_passive_queue_type               priority_queues
% 1.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.98  --inst_passive_queues_freq              [25;2]
% 1.82/0.98  --inst_dismatching                      true
% 1.82/0.98  --inst_eager_unprocessed_to_passive     true
% 1.82/0.98  --inst_prop_sim_given                   true
% 1.82/0.98  --inst_prop_sim_new                     false
% 1.82/0.98  --inst_subs_new                         false
% 1.82/0.98  --inst_eq_res_simp                      false
% 1.82/0.98  --inst_subs_given                       false
% 1.82/0.98  --inst_orphan_elimination               true
% 1.82/0.98  --inst_learning_loop_flag               true
% 1.82/0.98  --inst_learning_start                   3000
% 1.82/0.98  --inst_learning_factor                  2
% 1.82/0.98  --inst_start_prop_sim_after_learn       3
% 1.82/0.98  --inst_sel_renew                        solver
% 1.82/0.98  --inst_lit_activity_flag                true
% 1.82/0.98  --inst_restr_to_given                   false
% 1.82/0.98  --inst_activity_threshold               500
% 1.82/0.98  --inst_out_proof                        true
% 1.82/0.98  
% 1.82/0.98  ------ Resolution Options
% 1.82/0.98  
% 1.82/0.98  --resolution_flag                       true
% 1.82/0.98  --res_lit_sel                           adaptive
% 1.82/0.98  --res_lit_sel_side                      none
% 1.82/0.98  --res_ordering                          kbo
% 1.82/0.98  --res_to_prop_solver                    active
% 1.82/0.98  --res_prop_simpl_new                    false
% 1.82/0.98  --res_prop_simpl_given                  true
% 1.82/0.98  --res_passive_queue_type                priority_queues
% 1.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.98  --res_passive_queues_freq               [15;5]
% 1.82/0.98  --res_forward_subs                      full
% 1.82/0.98  --res_backward_subs                     full
% 1.82/0.98  --res_forward_subs_resolution           true
% 1.82/0.98  --res_backward_subs_resolution          true
% 1.82/0.98  --res_orphan_elimination                true
% 1.82/0.98  --res_time_limit                        2.
% 1.82/0.98  --res_out_proof                         true
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Options
% 1.82/0.98  
% 1.82/0.98  --superposition_flag                    true
% 1.82/0.98  --sup_passive_queue_type                priority_queues
% 1.82/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.98  --demod_completeness_check              fast
% 1.82/0.98  --demod_use_ground                      true
% 1.82/0.98  --sup_to_prop_solver                    passive
% 1.82/0.98  --sup_prop_simpl_new                    true
% 1.82/0.98  --sup_prop_simpl_given                  true
% 1.82/0.98  --sup_fun_splitting                     false
% 1.82/0.98  --sup_smt_interval                      50000
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Simplification Setup
% 1.82/0.98  
% 1.82/0.98  --sup_indices_passive                   []
% 1.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_full_bw                           [BwDemod]
% 1.82/0.98  --sup_immed_triv                        [TrivRules]
% 1.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_immed_bw_main                     []
% 1.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  
% 1.82/0.98  ------ Combination Options
% 1.82/0.98  
% 1.82/0.98  --comb_res_mult                         3
% 1.82/0.98  --comb_sup_mult                         2
% 1.82/0.98  --comb_inst_mult                        10
% 1.82/0.98  
% 1.82/0.98  ------ Debug Options
% 1.82/0.98  
% 1.82/0.98  --dbg_backtrace                         false
% 1.82/0.98  --dbg_dump_prop_clauses                 false
% 1.82/0.98  --dbg_dump_prop_clauses_file            -
% 1.82/0.98  --dbg_out_stat                          false
% 1.82/0.98  ------ Parsing...
% 1.82/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.82/0.98  ------ Proving...
% 1.82/0.98  ------ Problem Properties 
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  clauses                                 26
% 1.82/0.98  conjectures                             14
% 1.82/0.98  EPR                                     12
% 1.82/0.98  Horn                                    23
% 1.82/0.98  unary                                   15
% 1.82/0.98  binary                                  5
% 1.82/0.98  lits                                    59
% 1.82/0.98  lits eq                                 8
% 1.82/0.98  fd_pure                                 0
% 1.82/0.98  fd_pseudo                               0
% 1.82/0.98  fd_cond                                 0
% 1.82/0.98  fd_pseudo_cond                          0
% 1.82/0.98  AC symbols                              0
% 1.82/0.98  
% 1.82/0.98  ------ Schedule dynamic 5 is on 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  Current options:
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.82/0.98  
% 1.82/0.98  ------ Preprocessing Options
% 1.82/0.98  
% 1.82/0.98  --preprocessing_flag                    true
% 1.82/0.98  --time_out_prep_mult                    0.1
% 1.82/0.98  --splitting_mode                        input
% 1.82/0.98  --splitting_grd                         true
% 1.82/0.98  --splitting_cvd                         false
% 1.82/0.98  --splitting_cvd_svl                     false
% 1.82/0.98  --splitting_nvd                         32
% 1.82/0.98  --sub_typing                            true
% 1.82/0.98  --prep_gs_sim                           true
% 1.82/0.98  --prep_unflatten                        true
% 1.82/0.98  --prep_res_sim                          true
% 1.82/0.98  --prep_upred                            true
% 1.82/0.98  --prep_sem_filter                       exhaustive
% 1.82/0.98  --prep_sem_filter_out                   false
% 1.82/0.98  --pred_elim                             true
% 1.82/0.98  --res_sim_input                         true
% 1.82/0.98  --eq_ax_congr_red                       true
% 1.82/0.98  --pure_diseq_elim                       true
% 1.82/0.98  --brand_transform                       false
% 1.82/0.98  --non_eq_to_eq                          false
% 1.82/0.98  --prep_def_merge                        true
% 1.82/0.98  --prep_def_merge_prop_impl              false
% 1.82/0.98  --prep_def_merge_mbd                    true
% 1.82/0.98  --prep_def_merge_tr_red                 false
% 1.82/0.98  --prep_def_merge_tr_cl                  false
% 1.82/0.98  --smt_preprocessing                     true
% 1.82/0.98  --smt_ac_axioms                         fast
% 1.82/0.98  --preprocessed_out                      false
% 1.82/0.98  --preprocessed_stats                    false
% 1.82/0.98  
% 1.82/0.98  ------ Abstraction refinement Options
% 1.82/0.98  
% 1.82/0.98  --abstr_ref                             []
% 1.82/0.98  --abstr_ref_prep                        false
% 1.82/0.98  --abstr_ref_until_sat                   false
% 1.82/0.98  --abstr_ref_sig_restrict                funpre
% 1.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/0.98  --abstr_ref_under                       []
% 1.82/0.98  
% 1.82/0.98  ------ SAT Options
% 1.82/0.98  
% 1.82/0.98  --sat_mode                              false
% 1.82/0.98  --sat_fm_restart_options                ""
% 1.82/0.98  --sat_gr_def                            false
% 1.82/0.98  --sat_epr_types                         true
% 1.82/0.98  --sat_non_cyclic_types                  false
% 1.82/0.98  --sat_finite_models                     false
% 1.82/0.98  --sat_fm_lemmas                         false
% 1.82/0.98  --sat_fm_prep                           false
% 1.82/0.98  --sat_fm_uc_incr                        true
% 1.82/0.98  --sat_out_model                         small
% 1.82/0.98  --sat_out_clauses                       false
% 1.82/0.98  
% 1.82/0.98  ------ QBF Options
% 1.82/0.98  
% 1.82/0.98  --qbf_mode                              false
% 1.82/0.98  --qbf_elim_univ                         false
% 1.82/0.98  --qbf_dom_inst                          none
% 1.82/0.98  --qbf_dom_pre_inst                      false
% 1.82/0.98  --qbf_sk_in                             false
% 1.82/0.98  --qbf_pred_elim                         true
% 1.82/0.98  --qbf_split                             512
% 1.82/0.98  
% 1.82/0.98  ------ BMC1 Options
% 1.82/0.98  
% 1.82/0.98  --bmc1_incremental                      false
% 1.82/0.98  --bmc1_axioms                           reachable_all
% 1.82/0.98  --bmc1_min_bound                        0
% 1.82/0.98  --bmc1_max_bound                        -1
% 1.82/0.98  --bmc1_max_bound_default                -1
% 1.82/0.98  --bmc1_symbol_reachability              true
% 1.82/0.98  --bmc1_property_lemmas                  false
% 1.82/0.98  --bmc1_k_induction                      false
% 1.82/0.98  --bmc1_non_equiv_states                 false
% 1.82/0.98  --bmc1_deadlock                         false
% 1.82/0.98  --bmc1_ucm                              false
% 1.82/0.98  --bmc1_add_unsat_core                   none
% 1.82/0.98  --bmc1_unsat_core_children              false
% 1.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/0.98  --bmc1_out_stat                         full
% 1.82/0.98  --bmc1_ground_init                      false
% 1.82/0.98  --bmc1_pre_inst_next_state              false
% 1.82/0.98  --bmc1_pre_inst_state                   false
% 1.82/0.98  --bmc1_pre_inst_reach_state             false
% 1.82/0.98  --bmc1_out_unsat_core                   false
% 1.82/0.98  --bmc1_aig_witness_out                  false
% 1.82/0.98  --bmc1_verbose                          false
% 1.82/0.98  --bmc1_dump_clauses_tptp                false
% 1.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.82/0.98  --bmc1_dump_file                        -
% 1.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.82/0.98  --bmc1_ucm_extend_mode                  1
% 1.82/0.98  --bmc1_ucm_init_mode                    2
% 1.82/0.98  --bmc1_ucm_cone_mode                    none
% 1.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.82/0.98  --bmc1_ucm_relax_model                  4
% 1.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/0.98  --bmc1_ucm_layered_model                none
% 1.82/0.98  --bmc1_ucm_max_lemma_size               10
% 1.82/0.98  
% 1.82/0.98  ------ AIG Options
% 1.82/0.98  
% 1.82/0.98  --aig_mode                              false
% 1.82/0.98  
% 1.82/0.98  ------ Instantiation Options
% 1.82/0.98  
% 1.82/0.98  --instantiation_flag                    true
% 1.82/0.98  --inst_sos_flag                         false
% 1.82/0.98  --inst_sos_phase                        true
% 1.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/0.98  --inst_lit_sel_side                     none
% 1.82/0.98  --inst_solver_per_active                1400
% 1.82/0.98  --inst_solver_calls_frac                1.
% 1.82/0.98  --inst_passive_queue_type               priority_queues
% 1.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/0.98  --inst_passive_queues_freq              [25;2]
% 1.82/0.98  --inst_dismatching                      true
% 1.82/0.98  --inst_eager_unprocessed_to_passive     true
% 1.82/0.98  --inst_prop_sim_given                   true
% 1.82/0.98  --inst_prop_sim_new                     false
% 1.82/0.98  --inst_subs_new                         false
% 1.82/0.98  --inst_eq_res_simp                      false
% 1.82/0.98  --inst_subs_given                       false
% 1.82/0.98  --inst_orphan_elimination               true
% 1.82/0.98  --inst_learning_loop_flag               true
% 1.82/0.98  --inst_learning_start                   3000
% 1.82/0.98  --inst_learning_factor                  2
% 1.82/0.98  --inst_start_prop_sim_after_learn       3
% 1.82/0.98  --inst_sel_renew                        solver
% 1.82/0.98  --inst_lit_activity_flag                true
% 1.82/0.98  --inst_restr_to_given                   false
% 1.82/0.98  --inst_activity_threshold               500
% 1.82/0.98  --inst_out_proof                        true
% 1.82/0.98  
% 1.82/0.98  ------ Resolution Options
% 1.82/0.98  
% 1.82/0.98  --resolution_flag                       false
% 1.82/0.98  --res_lit_sel                           adaptive
% 1.82/0.98  --res_lit_sel_side                      none
% 1.82/0.98  --res_ordering                          kbo
% 1.82/0.98  --res_to_prop_solver                    active
% 1.82/0.98  --res_prop_simpl_new                    false
% 1.82/0.98  --res_prop_simpl_given                  true
% 1.82/0.98  --res_passive_queue_type                priority_queues
% 1.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/0.98  --res_passive_queues_freq               [15;5]
% 1.82/0.98  --res_forward_subs                      full
% 1.82/0.98  --res_backward_subs                     full
% 1.82/0.98  --res_forward_subs_resolution           true
% 1.82/0.98  --res_backward_subs_resolution          true
% 1.82/0.98  --res_orphan_elimination                true
% 1.82/0.98  --res_time_limit                        2.
% 1.82/0.98  --res_out_proof                         true
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Options
% 1.82/0.98  
% 1.82/0.98  --superposition_flag                    true
% 1.82/0.98  --sup_passive_queue_type                priority_queues
% 1.82/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.82/0.98  --demod_completeness_check              fast
% 1.82/0.98  --demod_use_ground                      true
% 1.82/0.98  --sup_to_prop_solver                    passive
% 1.82/0.98  --sup_prop_simpl_new                    true
% 1.82/0.98  --sup_prop_simpl_given                  true
% 1.82/0.98  --sup_fun_splitting                     false
% 1.82/0.98  --sup_smt_interval                      50000
% 1.82/0.98  
% 1.82/0.98  ------ Superposition Simplification Setup
% 1.82/0.98  
% 1.82/0.98  --sup_indices_passive                   []
% 1.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_full_bw                           [BwDemod]
% 1.82/0.98  --sup_immed_triv                        [TrivRules]
% 1.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_immed_bw_main                     []
% 1.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/0.98  
% 1.82/0.98  ------ Combination Options
% 1.82/0.98  
% 1.82/0.98  --comb_res_mult                         3
% 1.82/0.98  --comb_sup_mult                         2
% 1.82/0.98  --comb_inst_mult                        10
% 1.82/0.98  
% 1.82/0.98  ------ Debug Options
% 1.82/0.98  
% 1.82/0.98  --dbg_backtrace                         false
% 1.82/0.98  --dbg_dump_prop_clauses                 false
% 1.82/0.98  --dbg_dump_prop_clauses_file            -
% 1.82/0.98  --dbg_out_stat                          false
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  ------ Proving...
% 1.82/0.98  
% 1.82/0.98  
% 1.82/0.98  % SZS status Theorem for theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  fof(f10,conjecture,(
% 1.82/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)))))))))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f11,negated_conjecture,(
% 1.82/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)))))))))),
% 1.82/0.98    inference(negated_conjecture,[],[f10])).
% 1.82/0.98  
% 1.82/0.98  fof(f24,plain,(
% 1.82/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.82/0.98    inference(ennf_transformation,[],[f11])).
% 1.82/0.98  
% 1.82/0.98  fof(f25,plain,(
% 1.82/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.98    inference(flattening,[],[f24])).
% 1.82/0.98  
% 1.82/0.98  fof(f37,plain,(
% 1.82/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) => (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),sK6) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK6) & r2_hidden(sK6,u1_struct_0(X2)) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f36,plain,(
% 1.82/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK5),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK5,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f35,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,sK4,X2,X4),X5) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f34,plain,(
% 1.82/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,sK3,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(sK3)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f33,plain,(
% 1.82/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,sK2,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(sK2),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f32,plain,(
% 1.82/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(sK1,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f38,plain,(
% 1.82/0.98    (((((k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) & r2_hidden(sK6,u1_struct_0(sK3)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f25,f37,f36,f35,f34,f33,f32])).
% 1.82/0.98  
% 1.82/0.98  fof(f58,plain,(
% 1.82/0.98    m1_pre_topc(sK3,sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f8,axiom,(
% 1.82/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f20,plain,(
% 1.82/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.98    inference(ennf_transformation,[],[f8])).
% 1.82/0.98  
% 1.82/0.98  fof(f21,plain,(
% 1.82/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.98    inference(flattening,[],[f20])).
% 1.82/0.98  
% 1.82/0.98  fof(f48,plain,(
% 1.82/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f21])).
% 1.82/0.98  
% 1.82/0.98  fof(f62,plain,(
% 1.82/0.98    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f61,plain,(
% 1.82/0.98    v1_funct_1(sK5)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f63,plain,(
% 1.82/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f6,axiom,(
% 1.82/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f16,plain,(
% 1.82/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.82/0.98    inference(ennf_transformation,[],[f6])).
% 1.82/0.98  
% 1.82/0.98  fof(f17,plain,(
% 1.82/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.82/0.98    inference(flattening,[],[f16])).
% 1.82/0.98  
% 1.82/0.98  fof(f46,plain,(
% 1.82/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f17])).
% 1.82/0.98  
% 1.82/0.98  fof(f54,plain,(
% 1.82/0.98    ~v2_struct_0(sK2)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f55,plain,(
% 1.82/0.98    v2_pre_topc(sK2)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f56,plain,(
% 1.82/0.98    l1_pre_topc(sK2)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f7,axiom,(
% 1.82/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f18,plain,(
% 1.82/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.82/0.98    inference(ennf_transformation,[],[f7])).
% 1.82/0.98  
% 1.82/0.98  fof(f19,plain,(
% 1.82/0.98    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.82/0.98    inference(flattening,[],[f18])).
% 1.82/0.98  
% 1.82/0.98  fof(f47,plain,(
% 1.82/0.98    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f19])).
% 1.82/0.98  
% 1.82/0.98  fof(f2,axiom,(
% 1.82/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f12,plain,(
% 1.82/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.82/0.98    inference(ennf_transformation,[],[f2])).
% 1.82/0.98  
% 1.82/0.98  fof(f41,plain,(
% 1.82/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f12])).
% 1.82/0.98  
% 1.82/0.98  fof(f3,axiom,(
% 1.82/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f30,plain,(
% 1.82/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.82/0.98    inference(nnf_transformation,[],[f3])).
% 1.82/0.98  
% 1.82/0.98  fof(f43,plain,(
% 1.82/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f30])).
% 1.82/0.98  
% 1.82/0.98  fof(f9,axiom,(
% 1.82/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f22,plain,(
% 1.82/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.82/0.98    inference(ennf_transformation,[],[f9])).
% 1.82/0.98  
% 1.82/0.98  fof(f23,plain,(
% 1.82/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.82/0.98    inference(flattening,[],[f22])).
% 1.82/0.98  
% 1.82/0.98  fof(f31,plain,(
% 1.82/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.82/0.98    inference(nnf_transformation,[],[f23])).
% 1.82/0.98  
% 1.82/0.98  fof(f50,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f31])).
% 1.82/0.98  
% 1.82/0.98  fof(f5,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f15,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.98    inference(ennf_transformation,[],[f5])).
% 1.82/0.98  
% 1.82/0.98  fof(f45,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.82/0.98    inference(cnf_transformation,[],[f15])).
% 1.82/0.98  
% 1.82/0.98  fof(f4,axiom,(
% 1.82/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f13,plain,(
% 1.82/0.98    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.82/0.98    inference(ennf_transformation,[],[f4])).
% 1.82/0.98  
% 1.82/0.98  fof(f14,plain,(
% 1.82/0.98    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.82/0.98    inference(flattening,[],[f13])).
% 1.82/0.98  
% 1.82/0.98  fof(f44,plain,(
% 1.82/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f14])).
% 1.82/0.98  
% 1.82/0.98  fof(f66,plain,(
% 1.82/0.98    r2_hidden(sK6,u1_struct_0(sK3))),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f67,plain,(
% 1.82/0.98    k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f1,axiom,(
% 1.82/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.82/0.98  
% 1.82/0.98  fof(f26,plain,(
% 1.82/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.82/0.98    inference(nnf_transformation,[],[f1])).
% 1.82/0.98  
% 1.82/0.98  fof(f27,plain,(
% 1.82/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.82/0.98    inference(rectify,[],[f26])).
% 1.82/0.98  
% 1.82/0.98  fof(f28,plain,(
% 1.82/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.82/0.98    introduced(choice_axiom,[])).
% 1.82/0.98  
% 1.82/0.98  fof(f29,plain,(
% 1.82/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.82/0.98  
% 1.82/0.98  fof(f39,plain,(
% 1.82/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.82/0.98    inference(cnf_transformation,[],[f29])).
% 1.82/0.98  
% 1.82/0.98  fof(f65,plain,(
% 1.82/0.98    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f64,plain,(
% 1.82/0.98    m1_pre_topc(sK3,sK4)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f60,plain,(
% 1.82/0.98    m1_pre_topc(sK4,sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f53,plain,(
% 1.82/0.98    l1_pre_topc(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f52,plain,(
% 1.82/0.98    v2_pre_topc(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  fof(f51,plain,(
% 1.82/0.98    ~v2_struct_0(sK1)),
% 1.82/0.98    inference(cnf_transformation,[],[f38])).
% 1.82/0.98  
% 1.82/0.98  cnf(c_21,negated_conjecture,
% 1.82/0.98      ( m1_pre_topc(sK3,sK1) ),
% 1.82/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1718,negated_conjecture,
% 1.82/0.98      ( m1_pre_topc(sK3,sK1) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2379,plain,
% 1.82/0.98      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1718]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_9,plain,
% 1.82/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.82/0.98      | ~ m1_pre_topc(X3,X1)
% 1.82/0.98      | ~ m1_pre_topc(X3,X4)
% 1.82/0.98      | ~ m1_pre_topc(X1,X4)
% 1.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.82/0.98      | v2_struct_0(X4)
% 1.82/0.98      | v2_struct_0(X2)
% 1.82/0.98      | ~ v2_pre_topc(X2)
% 1.82/0.98      | ~ v2_pre_topc(X4)
% 1.82/0.98      | ~ l1_pre_topc(X2)
% 1.82/0.98      | ~ l1_pre_topc(X4)
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.82/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_17,negated_conjecture,
% 1.82/0.98      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 1.82/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_494,plain,
% 1.82/0.98      ( ~ m1_pre_topc(X0,X1)
% 1.82/0.98      | ~ m1_pre_topc(X0,X2)
% 1.82/0.98      | ~ m1_pre_topc(X1,X2)
% 1.82/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 1.82/0.98      | v2_struct_0(X4)
% 1.82/0.98      | v2_struct_0(X2)
% 1.82/0.98      | ~ v2_pre_topc(X4)
% 1.82/0.98      | ~ v2_pre_topc(X2)
% 1.82/0.98      | ~ l1_pre_topc(X4)
% 1.82/0.98      | ~ l1_pre_topc(X2)
% 1.82/0.98      | ~ v1_funct_1(X3)
% 1.82/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 1.82/0.98      | u1_struct_0(X1) != u1_struct_0(sK4)
% 1.82/0.98      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.82/0.98      | sK5 != X3 ),
% 1.82/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_495,plain,
% 1.82/0.98      ( ~ m1_pre_topc(X0,X1)
% 1.82/0.98      | ~ m1_pre_topc(X0,X2)
% 1.82/0.98      | ~ m1_pre_topc(X1,X2)
% 1.82/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 1.82/0.98      | v2_struct_0(X2)
% 1.82/0.98      | v2_struct_0(X3)
% 1.82/0.98      | ~ v2_pre_topc(X2)
% 1.82/0.98      | ~ v2_pre_topc(X3)
% 1.82/0.98      | ~ l1_pre_topc(X2)
% 1.82/0.98      | ~ l1_pre_topc(X3)
% 1.82/0.98      | ~ v1_funct_1(sK5)
% 1.82/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 1.82/0.98      | u1_struct_0(X1) != u1_struct_0(sK4)
% 1.82/0.98      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 1.82/0.98      inference(unflattening,[status(thm)],[c_494]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_18,negated_conjecture,
% 1.82/0.98      ( v1_funct_1(sK5) ),
% 1.82/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_499,plain,
% 1.82/0.98      ( ~ l1_pre_topc(X3)
% 1.82/0.98      | ~ l1_pre_topc(X2)
% 1.82/0.98      | ~ v2_pre_topc(X3)
% 1.82/0.98      | ~ v2_pre_topc(X2)
% 1.82/0.98      | v2_struct_0(X3)
% 1.82/0.98      | v2_struct_0(X2)
% 1.82/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 1.82/0.98      | ~ m1_pre_topc(X1,X2)
% 1.82/0.98      | ~ m1_pre_topc(X0,X2)
% 1.82/0.98      | ~ m1_pre_topc(X0,X1)
% 1.82/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 1.82/0.98      | u1_struct_0(X1) != u1_struct_0(sK4)
% 1.82/0.98      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 1.82/0.98      inference(global_propositional_subsumption,
% 1.82/0.98                [status(thm)],
% 1.82/0.98                [c_495,c_18]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_500,plain,
% 1.82/0.98      ( ~ m1_pre_topc(X0,X1)
% 1.82/0.98      | ~ m1_pre_topc(X0,X2)
% 1.82/0.98      | ~ m1_pre_topc(X1,X2)
% 1.82/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 1.82/0.98      | v2_struct_0(X2)
% 1.82/0.98      | v2_struct_0(X3)
% 1.82/0.98      | ~ v2_pre_topc(X2)
% 1.82/0.98      | ~ v2_pre_topc(X3)
% 1.82/0.98      | ~ l1_pre_topc(X2)
% 1.82/0.98      | ~ l1_pre_topc(X3)
% 1.82/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK5,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK5)
% 1.82/0.98      | u1_struct_0(X1) != u1_struct_0(sK4)
% 1.82/0.98      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 1.82/0.98      inference(renaming,[status(thm)],[c_499]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1707,plain,
% 1.82/0.98      ( ~ m1_pre_topc(X0_56,X1_56)
% 1.82/0.98      | ~ m1_pre_topc(X0_56,X2_56)
% 1.82/0.98      | ~ m1_pre_topc(X1_56,X2_56)
% 1.82/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X3_56))))
% 1.82/0.98      | v2_struct_0(X2_56)
% 1.82/0.98      | v2_struct_0(X3_56)
% 1.82/0.98      | ~ v2_pre_topc(X2_56)
% 1.82/0.98      | ~ v2_pre_topc(X3_56)
% 1.82/0.98      | ~ l1_pre_topc(X2_56)
% 1.82/0.98      | ~ l1_pre_topc(X3_56)
% 1.82/0.98      | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X3_56),sK5,u1_struct_0(X0_56)) = k3_tmap_1(X2_56,X3_56,X1_56,X0_56,sK5)
% 1.82/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK4)
% 1.82/0.98      | u1_struct_0(X3_56) != u1_struct_0(sK2) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_500]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2390,plain,
% 1.82/0.98      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK5,u1_struct_0(X2_56)) = k3_tmap_1(X3_56,X1_56,X0_56,X2_56,sK5)
% 1.82/0.98      | u1_struct_0(X0_56) != u1_struct_0(sK4)
% 1.82/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK2)
% 1.82/0.98      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 1.82/0.98      | m1_pre_topc(X2_56,X3_56) != iProver_top
% 1.82/0.98      | m1_pre_topc(X0_56,X3_56) != iProver_top
% 1.82/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 1.82/0.98      | v2_struct_0(X1_56) = iProver_top
% 1.82/0.98      | v2_struct_0(X3_56) = iProver_top
% 1.82/0.98      | v2_pre_topc(X1_56) != iProver_top
% 1.82/0.98      | v2_pre_topc(X3_56) != iProver_top
% 1.82/0.98      | l1_pre_topc(X1_56) != iProver_top
% 1.82/0.98      | l1_pre_topc(X3_56) != iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1707]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_3348,plain,
% 1.82/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(X0_56),sK5,u1_struct_0(X1_56)) = k3_tmap_1(X2_56,X0_56,sK4,X1_56,sK5)
% 1.82/0.98      | u1_struct_0(X0_56) != u1_struct_0(sK2)
% 1.82/0.98      | m1_pre_topc(X1_56,X2_56) != iProver_top
% 1.82/0.98      | m1_pre_topc(X1_56,sK4) != iProver_top
% 1.82/0.98      | m1_pre_topc(sK4,X2_56) != iProver_top
% 1.82/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_56)))) != iProver_top
% 1.82/0.98      | v2_struct_0(X2_56) = iProver_top
% 1.82/0.98      | v2_struct_0(X0_56) = iProver_top
% 1.82/0.98      | v2_pre_topc(X2_56) != iProver_top
% 1.82/0.98      | v2_pre_topc(X0_56) != iProver_top
% 1.82/0.98      | l1_pre_topc(X2_56) != iProver_top
% 1.82/0.98      | l1_pre_topc(X0_56) != iProver_top ),
% 1.82/0.98      inference(equality_resolution,[status(thm)],[c_2390]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_3596,plain,
% 1.82/0.98      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0_56)) = k3_tmap_1(X1_56,sK2,sK4,X0_56,sK5)
% 1.82/0.98      | m1_pre_topc(X0_56,X1_56) != iProver_top
% 1.82/0.98      | m1_pre_topc(X0_56,sK4) != iProver_top
% 1.82/0.98      | m1_pre_topc(sK4,X1_56) != iProver_top
% 1.82/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.82/0.98      | v2_struct_0(X1_56) = iProver_top
% 1.82/0.98      | v2_struct_0(sK2) = iProver_top
% 1.82/0.98      | v2_pre_topc(X1_56) != iProver_top
% 1.82/0.98      | v2_pre_topc(sK2) != iProver_top
% 1.82/0.98      | l1_pre_topc(X1_56) != iProver_top
% 1.82/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 1.82/0.98      inference(equality_resolution,[status(thm)],[c_3348]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_16,negated_conjecture,
% 1.82/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 1.82/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_1721,negated_conjecture,
% 1.82/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 1.82/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_2376,plain,
% 1.82/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 1.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1721]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_7,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.98      | ~ v1_funct_1(X0)
% 1.82/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.82/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.82/0.98  
% 1.82/0.98  cnf(c_575,plain,
% 1.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 1.82/0.99      | sK5 != X0 ),
% 1.82/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_576,plain,
% 1.82/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.82/0.99      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 1.82/0.99      inference(unflattening,[status(thm)],[c_575]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1704,plain,
% 1.82/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.82/0.99      | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_576]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2393,plain,
% 1.82/0.99      ( k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54)
% 1.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1704]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2872,plain,
% 1.82/0.99      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_2376,c_2393]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3597,plain,
% 1.82/0.99      ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
% 1.82/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 1.82/0.99      | m1_pre_topc(X1_56,sK4) != iProver_top
% 1.82/0.99      | m1_pre_topc(sK4,X0_56) != iProver_top
% 1.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 1.82/0.99      | v2_struct_0(X0_56) = iProver_top
% 1.82/0.99      | v2_struct_0(sK2) = iProver_top
% 1.82/0.99      | v2_pre_topc(X0_56) != iProver_top
% 1.82/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.82/0.99      | l1_pre_topc(X0_56) != iProver_top
% 1.82/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 1.82/0.99      inference(demodulation,[status(thm)],[c_3596,c_2872]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_25,negated_conjecture,
% 1.82/0.99      ( ~ v2_struct_0(sK2) ),
% 1.82/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_32,plain,
% 1.82/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_24,negated_conjecture,
% 1.82/0.99      ( v2_pre_topc(sK2) ),
% 1.82/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_33,plain,
% 1.82/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_23,negated_conjecture,
% 1.82/0.99      ( l1_pre_topc(sK2) ),
% 1.82/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_34,plain,
% 1.82/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_41,plain,
% 1.82/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3645,plain,
% 1.82/0.99      ( l1_pre_topc(X0_56) != iProver_top
% 1.82/0.99      | v2_struct_0(X0_56) = iProver_top
% 1.82/0.99      | k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
% 1.82/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 1.82/0.99      | m1_pre_topc(X1_56,sK4) != iProver_top
% 1.82/0.99      | m1_pre_topc(sK4,X0_56) != iProver_top
% 1.82/0.99      | v2_pre_topc(X0_56) != iProver_top ),
% 1.82/0.99      inference(global_propositional_subsumption,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_3597,c_32,c_33,c_34,c_41]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3646,plain,
% 1.82/0.99      ( k3_tmap_1(X0_56,sK2,sK4,X1_56,sK5) = k7_relat_1(sK5,u1_struct_0(X1_56))
% 1.82/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 1.82/0.99      | m1_pre_topc(X1_56,sK4) != iProver_top
% 1.82/0.99      | m1_pre_topc(sK4,X0_56) != iProver_top
% 1.82/0.99      | v2_struct_0(X0_56) = iProver_top
% 1.82/0.99      | v2_pre_topc(X0_56) != iProver_top
% 1.82/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 1.82/0.99      inference(renaming,[status(thm)],[c_3645]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3660,plain,
% 1.82/0.99      ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k7_relat_1(sK5,u1_struct_0(sK3))
% 1.82/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.82/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 1.82/0.99      | v2_struct_0(sK1) = iProver_top
% 1.82/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.82/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.82/0.99      inference(superposition,[status(thm)],[c_2379,c_3646]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1739,plain,
% 1.82/0.99      ( k1_funct_1(X0_54,X1_54) = k1_funct_1(X2_54,X3_54)
% 1.82/0.99      | X0_54 != X2_54
% 1.82/0.99      | X1_54 != X3_54 ),
% 1.82/0.99      theory(equality) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3298,plain,
% 1.82/0.99      ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6)
% 1.82/0.99      | k3_tmap_1(sK1,sK2,sK4,sK3,sK5) != k7_relat_1(sK5,u1_struct_0(sK3))
% 1.82/0.99      | sK6 != sK6 ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1739]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1734,plain,
% 1.82/0.99      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 1.82/0.99      theory(equality) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2599,plain,
% 1.82/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != X0_55
% 1.82/0.99      | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != X0_55
% 1.82/0.99      | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1734]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3284,plain,
% 1.82/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6)
% 1.82/0.99      | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6)
% 1.82/0.99      | k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_2599]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2651,plain,
% 1.82/0.99      ( X0_55 != X1_55
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != X1_55
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = X0_55 ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1734]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2901,plain,
% 1.82/0.99      ( X0_55 != k1_funct_1(sK5,sK6)
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = X0_55
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != k1_funct_1(sK5,sK6) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_2651]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3138,plain,
% 1.82/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6)
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) != k1_funct_1(sK5,sK6)
% 1.82/0.99      | k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) != k1_funct_1(sK5,sK6) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_2901]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_8,plain,
% 1.82/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.82/0.99      | ~ m1_subset_1(X3,X1)
% 1.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.99      | ~ v1_funct_1(X0)
% 1.82/0.99      | v1_xboole_0(X1)
% 1.82/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.82/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_473,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,X1)
% 1.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.82/0.99      | ~ v1_funct_1(X2)
% 1.82/0.99      | v1_xboole_0(X1)
% 1.82/0.99      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.82/0.99      | u1_struct_0(sK4) != X1
% 1.82/0.99      | u1_struct_0(sK2) != X3
% 1.82/0.99      | sK5 != X2 ),
% 1.82/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_474,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 1.82/0.99      | ~ v1_funct_1(sK5)
% 1.82/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK5,X0) ),
% 1.82/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_478,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK5,X0) ),
% 1.82/0.99      inference(global_propositional_subsumption,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_474,c_18,c_16]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1708,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 1.82/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,X0_54) = k1_funct_1(sK5,X0_54) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_478]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2795,plain,
% 1.82/0.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.82/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 1.82/0.99      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) = k1_funct_1(sK5,sK6) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1708]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.82/0.99      | ~ v1_xboole_0(X1)
% 1.82/0.99      | v1_xboole_0(X0) ),
% 1.82/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_3,plain,
% 1.82/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.82/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_196,plain,
% 1.82/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.82/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_254,plain,
% 1.82/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.82/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_196]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1710,plain,
% 1.82/0.99      ( ~ r1_tarski(X0_54,X1_54)
% 1.82/0.99      | ~ v1_xboole_0(X1_54)
% 1.82/0.99      | v1_xboole_0(X0_54) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_254]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2639,plain,
% 1.82/0.99      ( ~ r1_tarski(X0_54,u1_struct_0(sK4))
% 1.82/0.99      | v1_xboole_0(X0_54)
% 1.82/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1710]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2722,plain,
% 1.82/0.99      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 1.82/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.82/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_2639]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_10,plain,
% 1.82/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.82/0.99      | ~ m1_pre_topc(X2,X0)
% 1.82/0.99      | ~ m1_pre_topc(X2,X1)
% 1.82/0.99      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0))
% 1.82/0.99      | ~ v2_pre_topc(X1)
% 1.82/0.99      | ~ l1_pre_topc(X1) ),
% 1.82/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1726,plain,
% 1.82/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 1.82/0.99      | ~ m1_pre_topc(X2_56,X1_56)
% 1.82/0.99      | ~ m1_pre_topc(X2_56,X0_56)
% 1.82/0.99      | r1_tarski(u1_struct_0(X2_56),u1_struct_0(X0_56))
% 1.82/0.99      | ~ v2_pre_topc(X1_56)
% 1.82/0.99      | ~ l1_pre_topc(X1_56) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2630,plain,
% 1.82/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 1.82/0.99      | ~ m1_pre_topc(X1_56,sK1)
% 1.82/0.99      | ~ m1_pre_topc(X0_56,sK1)
% 1.82/0.99      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56))
% 1.82/0.99      | ~ v2_pre_topc(sK1)
% 1.82/0.99      | ~ l1_pre_topc(sK1) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1726]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2690,plain,
% 1.82/0.99      ( ~ m1_pre_topc(sK3,sK4)
% 1.82/0.99      | ~ m1_pre_topc(sK3,sK1)
% 1.82/0.99      | ~ m1_pre_topc(sK4,sK1)
% 1.82/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 1.82/0.99      | ~ v2_pre_topc(sK1)
% 1.82/0.99      | ~ l1_pre_topc(sK1) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_2630]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1731,plain,( X0_54 = X0_54 ),theory(equality) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2660,plain,
% 1.82/0.99      ( sK6 = sK6 ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1731]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_6,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.82/0.99      | v1_relat_1(X0) ),
% 1.82/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1727,plain,
% 1.82/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 1.82/0.99      | v1_relat_1(X0_54) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_2588,plain,
% 1.82/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 1.82/0.99      | v1_relat_1(sK5) ),
% 1.82/0.99      inference(instantiation,[status(thm)],[c_1727]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_5,plain,
% 1.82/0.99      ( ~ r2_hidden(X0,X1)
% 1.82/0.99      | ~ v1_relat_1(X2)
% 1.82/0.99      | ~ v1_funct_1(X2)
% 1.82/0.99      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 1.82/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_13,negated_conjecture,
% 1.82/0.99      ( r2_hidden(sK6,u1_struct_0(sK3)) ),
% 1.82/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_402,plain,
% 1.82/0.99      ( ~ v1_relat_1(X0)
% 1.82/0.99      | ~ v1_funct_1(X0)
% 1.82/0.99      | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
% 1.82/0.99      | u1_struct_0(sK3) != X1
% 1.82/0.99      | sK6 != X2 ),
% 1.82/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_403,plain,
% 1.82/0.99      ( ~ v1_relat_1(X0)
% 1.82/0.99      | ~ v1_funct_1(X0)
% 1.82/0.99      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK3)),sK6) = k1_funct_1(X0,sK6) ),
% 1.82/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_550,plain,
% 1.82/0.99      ( ~ v1_relat_1(X0)
% 1.82/0.99      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK3)),sK6) = k1_funct_1(X0,sK6)
% 1.82/0.99      | sK5 != X0 ),
% 1.82/0.99      inference(resolution_lifted,[status(thm)],[c_403,c_18]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_551,plain,
% 1.82/0.99      ( ~ v1_relat_1(sK5)
% 1.82/0.99      | k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) = k1_funct_1(sK5,sK6) ),
% 1.82/0.99      inference(unflattening,[status(thm)],[c_550]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1706,plain,
% 1.82/0.99      ( ~ v1_relat_1(sK5)
% 1.82/0.99      | k1_funct_1(k7_relat_1(sK5,u1_struct_0(sK3)),sK6) = k1_funct_1(sK5,sK6) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_551]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_12,negated_conjecture,
% 1.82/0.99      ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
% 1.82/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1724,negated_conjecture,
% 1.82/0.99      ( k1_funct_1(k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) != k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK6) ),
% 1.82/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_1,plain,
% 1.82/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.82/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_417,plain,
% 1.82/0.99      ( ~ v1_xboole_0(X0) | u1_struct_0(sK3) != X0 | sK6 != X1 ),
% 1.82/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_418,plain,
% 1.82/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.82/0.99      inference(unflattening,[status(thm)],[c_417]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_14,negated_conjecture,
% 1.82/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.82/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_15,negated_conjecture,
% 1.82/0.99      ( m1_pre_topc(sK3,sK4) ),
% 1.82/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_42,plain,
% 1.82/0.99      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_19,negated_conjecture,
% 1.82/0.99      ( m1_pre_topc(sK4,sK1) ),
% 1.82/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_38,plain,
% 1.82/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_26,negated_conjecture,
% 1.82/0.99      ( l1_pre_topc(sK1) ),
% 1.82/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_31,plain,
% 1.82/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_27,negated_conjecture,
% 1.82/0.99      ( v2_pre_topc(sK1) ),
% 1.82/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_30,plain,
% 1.82/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_28,negated_conjecture,
% 1.82/0.99      ( ~ v2_struct_0(sK1) ),
% 1.82/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(c_29,plain,
% 1.82/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 1.82/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.82/0.99  
% 1.82/0.99  cnf(contradiction,plain,
% 1.82/0.99      ( $false ),
% 1.82/0.99      inference(minisat,
% 1.82/0.99                [status(thm)],
% 1.82/0.99                [c_3660,c_3298,c_3284,c_3138,c_2795,c_2722,c_2690,c_2660,
% 1.82/0.99                 c_2588,c_1706,c_1724,c_418,c_14,c_42,c_15,c_16,c_38,
% 1.82/0.99                 c_19,c_21,c_31,c_26,c_30,c_27,c_29]) ).
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.82/0.99  
% 1.82/0.99  ------                               Statistics
% 1.82/0.99  
% 1.82/0.99  ------ General
% 1.82/0.99  
% 1.82/0.99  abstr_ref_over_cycles:                  0
% 1.82/0.99  abstr_ref_under_cycles:                 0
% 1.82/0.99  gc_basic_clause_elim:                   0
% 1.82/0.99  forced_gc_time:                         0
% 1.82/0.99  parsing_time:                           0.008
% 1.82/0.99  unif_index_cands_time:                  0.
% 1.82/0.99  unif_index_add_time:                    0.
% 1.82/0.99  orderings_time:                         0.
% 1.82/0.99  out_proof_time:                         0.008
% 1.82/0.99  total_time:                             0.124
% 1.82/0.99  num_of_symbols:                         60
% 1.82/0.99  num_of_terms:                           2435
% 1.82/0.99  
% 1.82/0.99  ------ Preprocessing
% 1.82/0.99  
% 1.82/0.99  num_of_splits:                          0
% 1.82/0.99  num_of_split_atoms:                     0
% 1.82/0.99  num_of_reused_defs:                     0
% 1.82/0.99  num_eq_ax_congr_red:                    18
% 1.82/0.99  num_of_sem_filtered_clauses:            1
% 1.82/0.99  num_of_subtypes:                        3
% 1.82/0.99  monotx_restored_types:                  0
% 1.82/0.99  sat_num_of_epr_types:                   0
% 1.82/0.99  sat_num_of_non_cyclic_types:            0
% 1.82/0.99  sat_guarded_non_collapsed_types:        0
% 1.82/0.99  num_pure_diseq_elim:                    0
% 1.82/0.99  simp_replaced_by:                       0
% 1.82/0.99  res_preprocessed:                       138
% 1.82/0.99  prep_upred:                             0
% 1.82/0.99  prep_unflattend:                        52
% 1.82/0.99  smt_new_axioms:                         0
% 1.82/0.99  pred_elim_cands:                        8
% 1.82/0.99  pred_elim:                              3
% 1.82/0.99  pred_elim_cl:                           3
% 1.82/0.99  pred_elim_cycles:                       11
% 1.82/0.99  merged_defs:                            8
% 1.82/0.99  merged_defs_ncl:                        0
% 1.82/0.99  bin_hyper_res:                          9
% 1.82/0.99  prep_cycles:                            4
% 1.82/0.99  pred_elim_time:                         0.023
% 1.82/0.99  splitting_time:                         0.
% 1.82/0.99  sem_filter_time:                        0.
% 1.82/0.99  monotx_time:                            0.
% 1.82/0.99  subtype_inf_time:                       0.
% 1.82/0.99  
% 1.82/0.99  ------ Problem properties
% 1.82/0.99  
% 1.82/0.99  clauses:                                26
% 1.82/0.99  conjectures:                            14
% 1.82/0.99  epr:                                    12
% 1.82/0.99  horn:                                   23
% 1.82/0.99  ground:                                 16
% 1.82/0.99  unary:                                  15
% 1.82/0.99  binary:                                 5
% 1.82/0.99  lits:                                   59
% 1.82/0.99  lits_eq:                                8
% 1.82/0.99  fd_pure:                                0
% 1.82/0.99  fd_pseudo:                              0
% 1.82/0.99  fd_cond:                                0
% 1.82/0.99  fd_pseudo_cond:                         0
% 1.82/0.99  ac_symbols:                             0
% 1.82/0.99  
% 1.82/0.99  ------ Propositional Solver
% 1.82/0.99  
% 1.82/0.99  prop_solver_calls:                      28
% 1.82/0.99  prop_fast_solver_calls:                 1064
% 1.82/0.99  smt_solver_calls:                       0
% 1.82/0.99  smt_fast_solver_calls:                  0
% 1.82/0.99  prop_num_of_clauses:                    704
% 1.82/0.99  prop_preprocess_simplified:             3699
% 1.82/0.99  prop_fo_subsumed:                       17
% 1.82/0.99  prop_solver_time:                       0.
% 1.82/0.99  smt_solver_time:                        0.
% 1.82/0.99  smt_fast_solver_time:                   0.
% 1.82/0.99  prop_fast_solver_time:                  0.
% 1.82/0.99  prop_unsat_core_time:                   0.
% 1.82/0.99  
% 1.82/0.99  ------ QBF
% 1.82/0.99  
% 1.82/0.99  qbf_q_res:                              0
% 1.82/0.99  qbf_num_tautologies:                    0
% 1.82/0.99  qbf_prep_cycles:                        0
% 1.82/0.99  
% 1.82/0.99  ------ BMC1
% 1.82/0.99  
% 1.82/0.99  bmc1_current_bound:                     -1
% 1.82/0.99  bmc1_last_solved_bound:                 -1
% 1.82/0.99  bmc1_unsat_core_size:                   -1
% 1.82/0.99  bmc1_unsat_core_parents_size:           -1
% 1.82/0.99  bmc1_merge_next_fun:                    0
% 1.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.82/0.99  
% 1.82/0.99  ------ Instantiation
% 1.82/0.99  
% 1.82/0.99  inst_num_of_clauses:                    225
% 1.82/0.99  inst_num_in_passive:                    25
% 1.82/0.99  inst_num_in_active:                     200
% 1.82/0.99  inst_num_in_unprocessed:                0
% 1.82/0.99  inst_num_of_loops:                      220
% 1.82/0.99  inst_num_of_learning_restarts:          0
% 1.82/0.99  inst_num_moves_active_passive:          13
% 1.82/0.99  inst_lit_activity:                      0
% 1.82/0.99  inst_lit_activity_moves:                0
% 1.82/0.99  inst_num_tautologies:                   0
% 1.82/0.99  inst_num_prop_implied:                  0
% 1.82/0.99  inst_num_existing_simplified:           0
% 1.82/0.99  inst_num_eq_res_simplified:             0
% 1.82/0.99  inst_num_child_elim:                    0
% 1.82/0.99  inst_num_of_dismatching_blockings:      19
% 1.82/0.99  inst_num_of_non_proper_insts:           248
% 1.82/0.99  inst_num_of_duplicates:                 0
% 1.82/0.99  inst_inst_num_from_inst_to_res:         0
% 1.82/0.99  inst_dismatching_checking_time:         0.
% 1.82/0.99  
% 1.82/0.99  ------ Resolution
% 1.82/0.99  
% 1.82/0.99  res_num_of_clauses:                     0
% 1.82/0.99  res_num_in_passive:                     0
% 1.82/0.99  res_num_in_active:                      0
% 1.82/0.99  res_num_of_loops:                       142
% 1.82/0.99  res_forward_subset_subsumed:            62
% 1.82/0.99  res_backward_subset_subsumed:           0
% 1.82/0.99  res_forward_subsumed:                   0
% 1.82/0.99  res_backward_subsumed:                  0
% 1.82/0.99  res_forward_subsumption_resolution:     0
% 1.82/0.99  res_backward_subsumption_resolution:    0
% 1.82/0.99  res_clause_to_clause_subsumption:       77
% 1.82/0.99  res_orphan_elimination:                 0
% 1.82/0.99  res_tautology_del:                      82
% 1.82/0.99  res_num_eq_res_simplified:              0
% 1.82/0.99  res_num_sel_changes:                    0
% 1.82/0.99  res_moves_from_active_to_pass:          0
% 1.82/0.99  
% 1.82/0.99  ------ Superposition
% 1.82/0.99  
% 1.82/0.99  sup_time_total:                         0.
% 1.82/0.99  sup_time_generating:                    0.
% 1.82/0.99  sup_time_sim_full:                      0.
% 1.82/0.99  sup_time_sim_immed:                     0.
% 1.82/0.99  
% 1.82/0.99  sup_num_of_clauses:                     48
% 1.82/0.99  sup_num_in_active:                      42
% 1.82/0.99  sup_num_in_passive:                     6
% 1.82/0.99  sup_num_of_loops:                       42
% 1.82/0.99  sup_fw_superposition:                   21
% 1.82/0.99  sup_bw_superposition:                   4
% 1.82/0.99  sup_immediate_simplified:               3
% 1.82/0.99  sup_given_eliminated:                   0
% 1.82/0.99  comparisons_done:                       0
% 1.82/0.99  comparisons_avoided:                    0
% 1.82/0.99  
% 1.82/0.99  ------ Simplifications
% 1.82/0.99  
% 1.82/0.99  
% 1.82/0.99  sim_fw_subset_subsumed:                 2
% 1.82/0.99  sim_bw_subset_subsumed:                 0
% 1.82/0.99  sim_fw_subsumed:                        0
% 1.82/0.99  sim_bw_subsumed:                        0
% 1.82/0.99  sim_fw_subsumption_res:                 0
% 1.82/0.99  sim_bw_subsumption_res:                 0
% 1.82/0.99  sim_tautology_del:                      4
% 1.82/0.99  sim_eq_tautology_del:                   0
% 1.82/0.99  sim_eq_res_simp:                        0
% 1.82/0.99  sim_fw_demodulated:                     1
% 1.82/0.99  sim_bw_demodulated:                     1
% 1.82/0.99  sim_light_normalised:                   0
% 1.82/0.99  sim_joinable_taut:                      0
% 1.82/0.99  sim_joinable_simp:                      0
% 1.82/0.99  sim_ac_normalised:                      0
% 1.82/0.99  sim_smt_subsumption:                    0
% 1.82/0.99  
%------------------------------------------------------------------------------
