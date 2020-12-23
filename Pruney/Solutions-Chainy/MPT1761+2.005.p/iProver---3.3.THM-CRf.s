%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:48 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 424 expanded)
%              Number of clauses        :   85 (  95 expanded)
%              Number of leaves         :   18 ( 187 expanded)
%              Depth                    :   19
%              Number of atoms          :  660 (5649 expanded)
%              Number of equality atoms :  188 ( 599 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),sK5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK5)
        & r2_hidden(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
            ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK4,X5)
            & r2_hidden(X5,u1_struct_0(X2))
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                ( k1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X4),X5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(X1),X4,X5)
                & r2_hidden(X5,u1_struct_0(X2))
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                    ( k1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                    & r2_hidden(X5,u1_struct_0(sK2))
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                        ( k1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5)
                        & r2_hidden(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
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
                          ( k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    & r2_hidden(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f31,f30,f29,f28,f27,f26])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1001,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1350,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_361,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_362,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,X3,X2,X0,sK4)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_366,plain,
    ( ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,X3,X2,X0,sK4)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_14])).

cnf(c_367,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_991,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ m1_pre_topc(X2_57,X1_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X3_57))))
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X3_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | u1_struct_0(X0_57) != u1_struct_0(sK3)
    | u1_struct_0(X3_57) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X3_57),sK4,u1_struct_0(X2_57)) = k3_tmap_1(X1_57,X3_57,X0_57,X2_57,sK4) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_1360,plain,
    ( u1_struct_0(X0_57) != u1_struct_0(sK3)
    | u1_struct_0(X1_57) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),sK4,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,sK4)
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_1978,plain,
    ( u1_struct_0(X0_57) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_57),sK4,u1_struct_0(X1_57)) = k3_tmap_1(X2_57,X0_57,sK3,X1_57,sK4)
    | m1_pre_topc(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X1_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X2_57) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57)))) != iProver_top
    | v2_pre_topc(X2_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X2_57) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1360])).

cnf(c_1995,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_57) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1978])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1004,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1347,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_990,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_1361,plain,
    ( k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_1775,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1347,c_1361])).

cnf(c_1996,plain,
    ( k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_57) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1995,c_1775])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2058,plain,
    ( l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_28,c_29,c_30,c_37])).

cnf(c_2059,plain,
    ( k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_2058])).

cnf(c_2073,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_2059])).

cnf(c_1017,plain,
    ( k1_funct_1(X0_53,X1_53) = k1_funct_1(X2_53,X3_53)
    | X0_53 != X2_53
    | X1_53 != X3_53 ),
    theory(equality)).

cnf(c_1857,plain,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k7_relat_1(sK4,u1_struct_0(sK2))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1016,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_1529,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_56
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_56
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1753,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1550,plain,
    ( X0_56 != X1_56
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X1_56
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_56 ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1654,plain,
    ( X0_56 != k1_funct_1(sK4,sK5)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_56
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_1672,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5)
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK1) != X3
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_345,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_14,c_12])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k1_funct_1(sK4,X0_53) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_1010,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1556,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1008,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ l1_pre_topc(X1_57)
    | l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1519,plain,
    ( ~ m1_pre_topc(X0_57,sK0)
    | l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_1521,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_252,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_253,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_417,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_253,c_14])).

cnf(c_418,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_418])).

cnf(c_446,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_989,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_446])).

cnf(c_1501,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_8,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1007,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_288,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_290,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2073,c_1857,c_1753,c_1672,c_1596,c_1556,c_1521,c_1501,c_1007,c_290,c_10,c_38,c_12,c_34,c_15,c_16,c_27,c_22,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.58/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.00  
% 1.58/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.58/1.00  
% 1.58/1.00  ------  iProver source info
% 1.58/1.00  
% 1.58/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.58/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.58/1.00  git: non_committed_changes: false
% 1.58/1.00  git: last_make_outside_of_git: false
% 1.58/1.00  
% 1.58/1.00  ------ 
% 1.58/1.00  
% 1.58/1.00  ------ Input Options
% 1.58/1.00  
% 1.58/1.00  --out_options                           all
% 1.58/1.00  --tptp_safe_out                         true
% 1.58/1.00  --problem_path                          ""
% 1.58/1.00  --include_path                          ""
% 1.58/1.00  --clausifier                            res/vclausify_rel
% 1.58/1.00  --clausifier_options                    --mode clausify
% 1.58/1.00  --stdin                                 false
% 1.58/1.00  --stats_out                             all
% 1.58/1.00  
% 1.58/1.00  ------ General Options
% 1.58/1.00  
% 1.58/1.00  --fof                                   false
% 1.58/1.00  --time_out_real                         305.
% 1.58/1.00  --time_out_virtual                      -1.
% 1.58/1.00  --symbol_type_check                     false
% 1.58/1.00  --clausify_out                          false
% 1.58/1.00  --sig_cnt_out                           false
% 1.58/1.00  --trig_cnt_out                          false
% 1.58/1.00  --trig_cnt_out_tolerance                1.
% 1.58/1.00  --trig_cnt_out_sk_spl                   false
% 1.58/1.00  --abstr_cl_out                          false
% 1.58/1.00  
% 1.58/1.00  ------ Global Options
% 1.58/1.00  
% 1.58/1.00  --schedule                              default
% 1.58/1.00  --add_important_lit                     false
% 1.58/1.00  --prop_solver_per_cl                    1000
% 1.58/1.00  --min_unsat_core                        false
% 1.58/1.00  --soft_assumptions                      false
% 1.58/1.00  --soft_lemma_size                       3
% 1.58/1.00  --prop_impl_unit_size                   0
% 1.58/1.00  --prop_impl_unit                        []
% 1.58/1.00  --share_sel_clauses                     true
% 1.58/1.00  --reset_solvers                         false
% 1.58/1.00  --bc_imp_inh                            [conj_cone]
% 1.58/1.00  --conj_cone_tolerance                   3.
% 1.58/1.00  --extra_neg_conj                        none
% 1.58/1.00  --large_theory_mode                     true
% 1.58/1.00  --prolific_symb_bound                   200
% 1.58/1.00  --lt_threshold                          2000
% 1.58/1.00  --clause_weak_htbl                      true
% 1.58/1.00  --gc_record_bc_elim                     false
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing Options
% 1.58/1.00  
% 1.58/1.00  --preprocessing_flag                    true
% 1.58/1.00  --time_out_prep_mult                    0.1
% 1.58/1.00  --splitting_mode                        input
% 1.58/1.00  --splitting_grd                         true
% 1.58/1.00  --splitting_cvd                         false
% 1.58/1.00  --splitting_cvd_svl                     false
% 1.58/1.00  --splitting_nvd                         32
% 1.58/1.00  --sub_typing                            true
% 1.58/1.00  --prep_gs_sim                           true
% 1.58/1.00  --prep_unflatten                        true
% 1.58/1.00  --prep_res_sim                          true
% 1.58/1.00  --prep_upred                            true
% 1.58/1.00  --prep_sem_filter                       exhaustive
% 1.58/1.00  --prep_sem_filter_out                   false
% 1.58/1.00  --pred_elim                             true
% 1.58/1.00  --res_sim_input                         true
% 1.58/1.00  --eq_ax_congr_red                       true
% 1.58/1.00  --pure_diseq_elim                       true
% 1.58/1.00  --brand_transform                       false
% 1.58/1.00  --non_eq_to_eq                          false
% 1.58/1.00  --prep_def_merge                        true
% 1.58/1.00  --prep_def_merge_prop_impl              false
% 1.58/1.00  --prep_def_merge_mbd                    true
% 1.58/1.00  --prep_def_merge_tr_red                 false
% 1.58/1.00  --prep_def_merge_tr_cl                  false
% 1.58/1.00  --smt_preprocessing                     true
% 1.58/1.00  --smt_ac_axioms                         fast
% 1.58/1.00  --preprocessed_out                      false
% 1.58/1.00  --preprocessed_stats                    false
% 1.58/1.00  
% 1.58/1.00  ------ Abstraction refinement Options
% 1.58/1.00  
% 1.58/1.00  --abstr_ref                             []
% 1.58/1.00  --abstr_ref_prep                        false
% 1.58/1.00  --abstr_ref_until_sat                   false
% 1.58/1.00  --abstr_ref_sig_restrict                funpre
% 1.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.00  --abstr_ref_under                       []
% 1.58/1.00  
% 1.58/1.00  ------ SAT Options
% 1.58/1.00  
% 1.58/1.00  --sat_mode                              false
% 1.58/1.00  --sat_fm_restart_options                ""
% 1.58/1.00  --sat_gr_def                            false
% 1.58/1.00  --sat_epr_types                         true
% 1.58/1.00  --sat_non_cyclic_types                  false
% 1.58/1.00  --sat_finite_models                     false
% 1.58/1.00  --sat_fm_lemmas                         false
% 1.58/1.00  --sat_fm_prep                           false
% 1.58/1.00  --sat_fm_uc_incr                        true
% 1.58/1.00  --sat_out_model                         small
% 1.58/1.00  --sat_out_clauses                       false
% 1.58/1.00  
% 1.58/1.00  ------ QBF Options
% 1.58/1.00  
% 1.58/1.00  --qbf_mode                              false
% 1.58/1.00  --qbf_elim_univ                         false
% 1.58/1.00  --qbf_dom_inst                          none
% 1.58/1.00  --qbf_dom_pre_inst                      false
% 1.58/1.00  --qbf_sk_in                             false
% 1.58/1.00  --qbf_pred_elim                         true
% 1.58/1.00  --qbf_split                             512
% 1.58/1.00  
% 1.58/1.00  ------ BMC1 Options
% 1.58/1.00  
% 1.58/1.00  --bmc1_incremental                      false
% 1.58/1.00  --bmc1_axioms                           reachable_all
% 1.58/1.00  --bmc1_min_bound                        0
% 1.58/1.00  --bmc1_max_bound                        -1
% 1.58/1.00  --bmc1_max_bound_default                -1
% 1.58/1.00  --bmc1_symbol_reachability              true
% 1.58/1.00  --bmc1_property_lemmas                  false
% 1.58/1.00  --bmc1_k_induction                      false
% 1.58/1.00  --bmc1_non_equiv_states                 false
% 1.58/1.00  --bmc1_deadlock                         false
% 1.58/1.00  --bmc1_ucm                              false
% 1.58/1.00  --bmc1_add_unsat_core                   none
% 1.58/1.00  --bmc1_unsat_core_children              false
% 1.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.00  --bmc1_out_stat                         full
% 1.58/1.00  --bmc1_ground_init                      false
% 1.58/1.00  --bmc1_pre_inst_next_state              false
% 1.58/1.00  --bmc1_pre_inst_state                   false
% 1.58/1.00  --bmc1_pre_inst_reach_state             false
% 1.58/1.00  --bmc1_out_unsat_core                   false
% 1.58/1.00  --bmc1_aig_witness_out                  false
% 1.58/1.00  --bmc1_verbose                          false
% 1.58/1.00  --bmc1_dump_clauses_tptp                false
% 1.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.00  --bmc1_dump_file                        -
% 1.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.00  --bmc1_ucm_extend_mode                  1
% 1.58/1.00  --bmc1_ucm_init_mode                    2
% 1.58/1.00  --bmc1_ucm_cone_mode                    none
% 1.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.00  --bmc1_ucm_relax_model                  4
% 1.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.00  --bmc1_ucm_layered_model                none
% 1.58/1.00  --bmc1_ucm_max_lemma_size               10
% 1.58/1.00  
% 1.58/1.00  ------ AIG Options
% 1.58/1.00  
% 1.58/1.00  --aig_mode                              false
% 1.58/1.00  
% 1.58/1.00  ------ Instantiation Options
% 1.58/1.00  
% 1.58/1.00  --instantiation_flag                    true
% 1.58/1.00  --inst_sos_flag                         false
% 1.58/1.00  --inst_sos_phase                        true
% 1.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.00  --inst_lit_sel_side                     num_symb
% 1.58/1.00  --inst_solver_per_active                1400
% 1.58/1.00  --inst_solver_calls_frac                1.
% 1.58/1.00  --inst_passive_queue_type               priority_queues
% 1.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.00  --inst_passive_queues_freq              [25;2]
% 1.58/1.00  --inst_dismatching                      true
% 1.58/1.00  --inst_eager_unprocessed_to_passive     true
% 1.58/1.00  --inst_prop_sim_given                   true
% 1.58/1.00  --inst_prop_sim_new                     false
% 1.58/1.00  --inst_subs_new                         false
% 1.58/1.00  --inst_eq_res_simp                      false
% 1.58/1.00  --inst_subs_given                       false
% 1.58/1.00  --inst_orphan_elimination               true
% 1.58/1.00  --inst_learning_loop_flag               true
% 1.58/1.00  --inst_learning_start                   3000
% 1.58/1.00  --inst_learning_factor                  2
% 1.58/1.00  --inst_start_prop_sim_after_learn       3
% 1.58/1.00  --inst_sel_renew                        solver
% 1.58/1.00  --inst_lit_activity_flag                true
% 1.58/1.00  --inst_restr_to_given                   false
% 1.58/1.00  --inst_activity_threshold               500
% 1.58/1.00  --inst_out_proof                        true
% 1.58/1.00  
% 1.58/1.00  ------ Resolution Options
% 1.58/1.00  
% 1.58/1.00  --resolution_flag                       true
% 1.58/1.00  --res_lit_sel                           adaptive
% 1.58/1.00  --res_lit_sel_side                      none
% 1.58/1.00  --res_ordering                          kbo
% 1.58/1.00  --res_to_prop_solver                    active
% 1.58/1.00  --res_prop_simpl_new                    false
% 1.58/1.00  --res_prop_simpl_given                  true
% 1.58/1.00  --res_passive_queue_type                priority_queues
% 1.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.00  --res_passive_queues_freq               [15;5]
% 1.58/1.00  --res_forward_subs                      full
% 1.58/1.00  --res_backward_subs                     full
% 1.58/1.00  --res_forward_subs_resolution           true
% 1.58/1.00  --res_backward_subs_resolution          true
% 1.58/1.00  --res_orphan_elimination                true
% 1.58/1.00  --res_time_limit                        2.
% 1.58/1.00  --res_out_proof                         true
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Options
% 1.58/1.00  
% 1.58/1.00  --superposition_flag                    true
% 1.58/1.00  --sup_passive_queue_type                priority_queues
% 1.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.00  --demod_completeness_check              fast
% 1.58/1.00  --demod_use_ground                      true
% 1.58/1.00  --sup_to_prop_solver                    passive
% 1.58/1.00  --sup_prop_simpl_new                    true
% 1.58/1.00  --sup_prop_simpl_given                  true
% 1.58/1.00  --sup_fun_splitting                     false
% 1.58/1.00  --sup_smt_interval                      50000
% 1.58/1.00  
% 1.58/1.00  ------ Superposition Simplification Setup
% 1.58/1.00  
% 1.58/1.00  --sup_indices_passive                   []
% 1.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_full_bw                           [BwDemod]
% 1.58/1.00  --sup_immed_triv                        [TrivRules]
% 1.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_immed_bw_main                     []
% 1.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.00  
% 1.58/1.00  ------ Combination Options
% 1.58/1.00  
% 1.58/1.00  --comb_res_mult                         3
% 1.58/1.00  --comb_sup_mult                         2
% 1.58/1.00  --comb_inst_mult                        10
% 1.58/1.00  
% 1.58/1.00  ------ Debug Options
% 1.58/1.00  
% 1.58/1.00  --dbg_backtrace                         false
% 1.58/1.00  --dbg_dump_prop_clauses                 false
% 1.58/1.00  --dbg_dump_prop_clauses_file            -
% 1.58/1.00  --dbg_out_stat                          false
% 1.58/1.00  ------ Parsing...
% 1.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.58/1.00  
% 1.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.58/1.00  ------ Proving...
% 1.58/1.00  ------ Problem Properties 
% 1.58/1.00  
% 1.58/1.00  
% 1.58/1.00  clauses                                 20
% 1.58/1.00  conjectures                             14
% 1.58/1.01  EPR                                     12
% 1.58/1.01  Horn                                    18
% 1.58/1.01  unary                                   14
% 1.58/1.01  binary                                  2
% 1.58/1.01  lits                                    40
% 1.58/1.01  lits eq                                 7
% 1.58/1.01  fd_pure                                 0
% 1.58/1.01  fd_pseudo                               0
% 1.58/1.01  fd_cond                                 0
% 1.58/1.01  fd_pseudo_cond                          0
% 1.58/1.01  AC symbols                              0
% 1.58/1.01  
% 1.58/1.01  ------ Schedule dynamic 5 is on 
% 1.58/1.01  
% 1.58/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  ------ 
% 1.58/1.01  Current options:
% 1.58/1.01  ------ 
% 1.58/1.01  
% 1.58/1.01  ------ Input Options
% 1.58/1.01  
% 1.58/1.01  --out_options                           all
% 1.58/1.01  --tptp_safe_out                         true
% 1.58/1.01  --problem_path                          ""
% 1.58/1.01  --include_path                          ""
% 1.58/1.01  --clausifier                            res/vclausify_rel
% 1.58/1.01  --clausifier_options                    --mode clausify
% 1.58/1.01  --stdin                                 false
% 1.58/1.01  --stats_out                             all
% 1.58/1.01  
% 1.58/1.01  ------ General Options
% 1.58/1.01  
% 1.58/1.01  --fof                                   false
% 1.58/1.01  --time_out_real                         305.
% 1.58/1.01  --time_out_virtual                      -1.
% 1.58/1.01  --symbol_type_check                     false
% 1.58/1.01  --clausify_out                          false
% 1.58/1.01  --sig_cnt_out                           false
% 1.58/1.01  --trig_cnt_out                          false
% 1.58/1.01  --trig_cnt_out_tolerance                1.
% 1.58/1.01  --trig_cnt_out_sk_spl                   false
% 1.58/1.01  --abstr_cl_out                          false
% 1.58/1.01  
% 1.58/1.01  ------ Global Options
% 1.58/1.01  
% 1.58/1.01  --schedule                              default
% 1.58/1.01  --add_important_lit                     false
% 1.58/1.01  --prop_solver_per_cl                    1000
% 1.58/1.01  --min_unsat_core                        false
% 1.58/1.01  --soft_assumptions                      false
% 1.58/1.01  --soft_lemma_size                       3
% 1.58/1.01  --prop_impl_unit_size                   0
% 1.58/1.01  --prop_impl_unit                        []
% 1.58/1.01  --share_sel_clauses                     true
% 1.58/1.01  --reset_solvers                         false
% 1.58/1.01  --bc_imp_inh                            [conj_cone]
% 1.58/1.01  --conj_cone_tolerance                   3.
% 1.58/1.01  --extra_neg_conj                        none
% 1.58/1.01  --large_theory_mode                     true
% 1.58/1.01  --prolific_symb_bound                   200
% 1.58/1.01  --lt_threshold                          2000
% 1.58/1.01  --clause_weak_htbl                      true
% 1.58/1.01  --gc_record_bc_elim                     false
% 1.58/1.01  
% 1.58/1.01  ------ Preprocessing Options
% 1.58/1.01  
% 1.58/1.01  --preprocessing_flag                    true
% 1.58/1.01  --time_out_prep_mult                    0.1
% 1.58/1.01  --splitting_mode                        input
% 1.58/1.01  --splitting_grd                         true
% 1.58/1.01  --splitting_cvd                         false
% 1.58/1.01  --splitting_cvd_svl                     false
% 1.58/1.01  --splitting_nvd                         32
% 1.58/1.01  --sub_typing                            true
% 1.58/1.01  --prep_gs_sim                           true
% 1.58/1.01  --prep_unflatten                        true
% 1.58/1.01  --prep_res_sim                          true
% 1.58/1.01  --prep_upred                            true
% 1.58/1.01  --prep_sem_filter                       exhaustive
% 1.58/1.01  --prep_sem_filter_out                   false
% 1.58/1.01  --pred_elim                             true
% 1.58/1.01  --res_sim_input                         true
% 1.58/1.01  --eq_ax_congr_red                       true
% 1.58/1.01  --pure_diseq_elim                       true
% 1.58/1.01  --brand_transform                       false
% 1.58/1.01  --non_eq_to_eq                          false
% 1.58/1.01  --prep_def_merge                        true
% 1.58/1.01  --prep_def_merge_prop_impl              false
% 1.58/1.01  --prep_def_merge_mbd                    true
% 1.58/1.01  --prep_def_merge_tr_red                 false
% 1.58/1.01  --prep_def_merge_tr_cl                  false
% 1.58/1.01  --smt_preprocessing                     true
% 1.58/1.01  --smt_ac_axioms                         fast
% 1.58/1.01  --preprocessed_out                      false
% 1.58/1.01  --preprocessed_stats                    false
% 1.58/1.01  
% 1.58/1.01  ------ Abstraction refinement Options
% 1.58/1.01  
% 1.58/1.01  --abstr_ref                             []
% 1.58/1.01  --abstr_ref_prep                        false
% 1.58/1.01  --abstr_ref_until_sat                   false
% 1.58/1.01  --abstr_ref_sig_restrict                funpre
% 1.58/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.01  --abstr_ref_under                       []
% 1.58/1.01  
% 1.58/1.01  ------ SAT Options
% 1.58/1.01  
% 1.58/1.01  --sat_mode                              false
% 1.58/1.01  --sat_fm_restart_options                ""
% 1.58/1.01  --sat_gr_def                            false
% 1.58/1.01  --sat_epr_types                         true
% 1.58/1.01  --sat_non_cyclic_types                  false
% 1.58/1.01  --sat_finite_models                     false
% 1.58/1.01  --sat_fm_lemmas                         false
% 1.58/1.01  --sat_fm_prep                           false
% 1.58/1.01  --sat_fm_uc_incr                        true
% 1.58/1.01  --sat_out_model                         small
% 1.58/1.01  --sat_out_clauses                       false
% 1.58/1.01  
% 1.58/1.01  ------ QBF Options
% 1.58/1.01  
% 1.58/1.01  --qbf_mode                              false
% 1.58/1.01  --qbf_elim_univ                         false
% 1.58/1.01  --qbf_dom_inst                          none
% 1.58/1.01  --qbf_dom_pre_inst                      false
% 1.58/1.01  --qbf_sk_in                             false
% 1.58/1.01  --qbf_pred_elim                         true
% 1.58/1.01  --qbf_split                             512
% 1.58/1.01  
% 1.58/1.01  ------ BMC1 Options
% 1.58/1.01  
% 1.58/1.01  --bmc1_incremental                      false
% 1.58/1.01  --bmc1_axioms                           reachable_all
% 1.58/1.01  --bmc1_min_bound                        0
% 1.58/1.01  --bmc1_max_bound                        -1
% 1.58/1.01  --bmc1_max_bound_default                -1
% 1.58/1.01  --bmc1_symbol_reachability              true
% 1.58/1.01  --bmc1_property_lemmas                  false
% 1.58/1.01  --bmc1_k_induction                      false
% 1.58/1.01  --bmc1_non_equiv_states                 false
% 1.58/1.01  --bmc1_deadlock                         false
% 1.58/1.01  --bmc1_ucm                              false
% 1.58/1.01  --bmc1_add_unsat_core                   none
% 1.58/1.01  --bmc1_unsat_core_children              false
% 1.58/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.01  --bmc1_out_stat                         full
% 1.58/1.01  --bmc1_ground_init                      false
% 1.58/1.01  --bmc1_pre_inst_next_state              false
% 1.58/1.01  --bmc1_pre_inst_state                   false
% 1.58/1.01  --bmc1_pre_inst_reach_state             false
% 1.58/1.01  --bmc1_out_unsat_core                   false
% 1.58/1.01  --bmc1_aig_witness_out                  false
% 1.58/1.01  --bmc1_verbose                          false
% 1.58/1.01  --bmc1_dump_clauses_tptp                false
% 1.58/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.01  --bmc1_dump_file                        -
% 1.58/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.01  --bmc1_ucm_extend_mode                  1
% 1.58/1.01  --bmc1_ucm_init_mode                    2
% 1.58/1.01  --bmc1_ucm_cone_mode                    none
% 1.58/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.01  --bmc1_ucm_relax_model                  4
% 1.58/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.01  --bmc1_ucm_layered_model                none
% 1.58/1.01  --bmc1_ucm_max_lemma_size               10
% 1.58/1.01  
% 1.58/1.01  ------ AIG Options
% 1.58/1.01  
% 1.58/1.01  --aig_mode                              false
% 1.58/1.01  
% 1.58/1.01  ------ Instantiation Options
% 1.58/1.01  
% 1.58/1.01  --instantiation_flag                    true
% 1.58/1.01  --inst_sos_flag                         false
% 1.58/1.01  --inst_sos_phase                        true
% 1.58/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.01  --inst_lit_sel_side                     none
% 1.58/1.01  --inst_solver_per_active                1400
% 1.58/1.01  --inst_solver_calls_frac                1.
% 1.58/1.01  --inst_passive_queue_type               priority_queues
% 1.58/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.01  --inst_passive_queues_freq              [25;2]
% 1.58/1.01  --inst_dismatching                      true
% 1.58/1.01  --inst_eager_unprocessed_to_passive     true
% 1.58/1.01  --inst_prop_sim_given                   true
% 1.58/1.01  --inst_prop_sim_new                     false
% 1.58/1.01  --inst_subs_new                         false
% 1.58/1.01  --inst_eq_res_simp                      false
% 1.58/1.01  --inst_subs_given                       false
% 1.58/1.01  --inst_orphan_elimination               true
% 1.58/1.01  --inst_learning_loop_flag               true
% 1.58/1.01  --inst_learning_start                   3000
% 1.58/1.01  --inst_learning_factor                  2
% 1.58/1.01  --inst_start_prop_sim_after_learn       3
% 1.58/1.01  --inst_sel_renew                        solver
% 1.58/1.01  --inst_lit_activity_flag                true
% 1.58/1.01  --inst_restr_to_given                   false
% 1.58/1.01  --inst_activity_threshold               500
% 1.58/1.01  --inst_out_proof                        true
% 1.58/1.01  
% 1.58/1.01  ------ Resolution Options
% 1.58/1.01  
% 1.58/1.01  --resolution_flag                       false
% 1.58/1.01  --res_lit_sel                           adaptive
% 1.58/1.01  --res_lit_sel_side                      none
% 1.58/1.01  --res_ordering                          kbo
% 1.58/1.01  --res_to_prop_solver                    active
% 1.58/1.01  --res_prop_simpl_new                    false
% 1.58/1.01  --res_prop_simpl_given                  true
% 1.58/1.01  --res_passive_queue_type                priority_queues
% 1.58/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.01  --res_passive_queues_freq               [15;5]
% 1.58/1.01  --res_forward_subs                      full
% 1.58/1.01  --res_backward_subs                     full
% 1.58/1.01  --res_forward_subs_resolution           true
% 1.58/1.01  --res_backward_subs_resolution          true
% 1.58/1.01  --res_orphan_elimination                true
% 1.58/1.01  --res_time_limit                        2.
% 1.58/1.01  --res_out_proof                         true
% 1.58/1.01  
% 1.58/1.01  ------ Superposition Options
% 1.58/1.01  
% 1.58/1.01  --superposition_flag                    true
% 1.58/1.01  --sup_passive_queue_type                priority_queues
% 1.58/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.01  --demod_completeness_check              fast
% 1.58/1.01  --demod_use_ground                      true
% 1.58/1.01  --sup_to_prop_solver                    passive
% 1.58/1.01  --sup_prop_simpl_new                    true
% 1.58/1.01  --sup_prop_simpl_given                  true
% 1.58/1.01  --sup_fun_splitting                     false
% 1.58/1.01  --sup_smt_interval                      50000
% 1.58/1.01  
% 1.58/1.01  ------ Superposition Simplification Setup
% 1.58/1.01  
% 1.58/1.01  --sup_indices_passive                   []
% 1.58/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.01  --sup_full_bw                           [BwDemod]
% 1.58/1.01  --sup_immed_triv                        [TrivRules]
% 1.58/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.01  --sup_immed_bw_main                     []
% 1.58/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.01  
% 1.58/1.01  ------ Combination Options
% 1.58/1.01  
% 1.58/1.01  --comb_res_mult                         3
% 1.58/1.01  --comb_sup_mult                         2
% 1.58/1.01  --comb_inst_mult                        10
% 1.58/1.01  
% 1.58/1.01  ------ Debug Options
% 1.58/1.01  
% 1.58/1.01  --dbg_backtrace                         false
% 1.58/1.01  --dbg_dump_prop_clauses                 false
% 1.58/1.01  --dbg_dump_prop_clauses_file            -
% 1.58/1.01  --dbg_out_stat                          false
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  ------ Proving...
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  % SZS status Theorem for theBenchmark.p
% 1.58/1.01  
% 1.58/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.58/1.01  
% 1.58/1.01  fof(f9,conjecture,(
% 1.58/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)))))))))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f10,negated_conjecture,(
% 1.58/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)))))))))),
% 1.58/1.01    inference(negated_conjecture,[],[f9])).
% 1.58/1.01  
% 1.58/1.01  fof(f24,plain,(
% 1.58/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.58/1.01    inference(ennf_transformation,[],[f10])).
% 1.58/1.01  
% 1.58/1.01  fof(f25,plain,(
% 1.58/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.58/1.01    inference(flattening,[],[f24])).
% 1.58/1.01  
% 1.58/1.01  fof(f31,plain,(
% 1.58/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) => (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),sK5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) & r2_hidden(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.58/1.01    introduced(choice_axiom,[])).
% 1.58/1.01  
% 1.58/1.01  fof(f30,plain,(
% 1.58/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.58/1.01    introduced(choice_axiom,[])).
% 1.58/1.01  
% 1.58/1.01  fof(f29,plain,(
% 1.58/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X4),X5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.58/1.01    introduced(choice_axiom,[])).
% 1.58/1.01  
% 1.58/1.01  fof(f28,plain,(
% 1.58/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.58/1.01    introduced(choice_axiom,[])).
% 1.58/1.01  
% 1.58/1.01  fof(f27,plain,(
% 1.58/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.58/1.01    introduced(choice_axiom,[])).
% 1.58/1.01  
% 1.58/1.01  fof(f26,plain,(
% 1.58/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.58/1.01    introduced(choice_axiom,[])).
% 1.58/1.01  
% 1.58/1.01  fof(f32,plain,(
% 1.58/1.01    (((((k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) & r2_hidden(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.58/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f31,f30,f29,f28,f27,f26])).
% 1.58/1.01  
% 1.58/1.01  fof(f48,plain,(
% 1.58/1.01    m1_pre_topc(sK2,sK0)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f8,axiom,(
% 1.58/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f22,plain,(
% 1.58/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/1.01    inference(ennf_transformation,[],[f8])).
% 1.58/1.01  
% 1.58/1.01  fof(f23,plain,(
% 1.58/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.01    inference(flattening,[],[f22])).
% 1.58/1.01  
% 1.58/1.01  fof(f40,plain,(
% 1.58/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f23])).
% 1.58/1.01  
% 1.58/1.01  fof(f52,plain,(
% 1.58/1.01    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f51,plain,(
% 1.58/1.01    v1_funct_1(sK4)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f53,plain,(
% 1.58/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f3,axiom,(
% 1.58/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f14,plain,(
% 1.58/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.58/1.01    inference(ennf_transformation,[],[f3])).
% 1.58/1.01  
% 1.58/1.01  fof(f15,plain,(
% 1.58/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.58/1.01    inference(flattening,[],[f14])).
% 1.58/1.01  
% 1.58/1.01  fof(f35,plain,(
% 1.58/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f15])).
% 1.58/1.01  
% 1.58/1.01  fof(f44,plain,(
% 1.58/1.01    ~v2_struct_0(sK1)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f45,plain,(
% 1.58/1.01    v2_pre_topc(sK1)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f46,plain,(
% 1.58/1.01    l1_pre_topc(sK1)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f4,axiom,(
% 1.58/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f16,plain,(
% 1.58/1.01    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.58/1.01    inference(ennf_transformation,[],[f4])).
% 1.58/1.01  
% 1.58/1.01  fof(f17,plain,(
% 1.58/1.01    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.58/1.01    inference(flattening,[],[f16])).
% 1.58/1.01  
% 1.58/1.01  fof(f36,plain,(
% 1.58/1.01    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f17])).
% 1.58/1.01  
% 1.58/1.01  fof(f6,axiom,(
% 1.58/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f19,plain,(
% 1.58/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/1.01    inference(ennf_transformation,[],[f6])).
% 1.58/1.01  
% 1.58/1.01  fof(f38,plain,(
% 1.58/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f19])).
% 1.58/1.01  
% 1.58/1.01  fof(f2,axiom,(
% 1.58/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f13,plain,(
% 1.58/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/1.01    inference(ennf_transformation,[],[f2])).
% 1.58/1.01  
% 1.58/1.01  fof(f34,plain,(
% 1.58/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/1.01    inference(cnf_transformation,[],[f13])).
% 1.58/1.01  
% 1.58/1.01  fof(f1,axiom,(
% 1.58/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f11,plain,(
% 1.58/1.01    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.58/1.01    inference(ennf_transformation,[],[f1])).
% 1.58/1.01  
% 1.58/1.01  fof(f12,plain,(
% 1.58/1.01    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.58/1.01    inference(flattening,[],[f11])).
% 1.58/1.01  
% 1.58/1.01  fof(f33,plain,(
% 1.58/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f12])).
% 1.58/1.01  
% 1.58/1.01  fof(f56,plain,(
% 1.58/1.01    r2_hidden(sK5,u1_struct_0(sK2))),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f57,plain,(
% 1.58/1.01    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f5,axiom,(
% 1.58/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f18,plain,(
% 1.58/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.58/1.01    inference(ennf_transformation,[],[f5])).
% 1.58/1.01  
% 1.58/1.01  fof(f37,plain,(
% 1.58/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f18])).
% 1.58/1.01  
% 1.58/1.01  fof(f7,axiom,(
% 1.58/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.58/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.01  
% 1.58/1.01  fof(f20,plain,(
% 1.58/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.58/1.01    inference(ennf_transformation,[],[f7])).
% 1.58/1.01  
% 1.58/1.01  fof(f21,plain,(
% 1.58/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.58/1.01    inference(flattening,[],[f20])).
% 1.58/1.01  
% 1.58/1.01  fof(f39,plain,(
% 1.58/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.58/1.01    inference(cnf_transformation,[],[f21])).
% 1.58/1.01  
% 1.58/1.01  fof(f55,plain,(
% 1.58/1.01    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f54,plain,(
% 1.58/1.01    m1_pre_topc(sK2,sK3)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f50,plain,(
% 1.58/1.01    m1_pre_topc(sK3,sK0)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f49,plain,(
% 1.58/1.01    ~v2_struct_0(sK3)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f43,plain,(
% 1.58/1.01    l1_pre_topc(sK0)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f42,plain,(
% 1.58/1.01    v2_pre_topc(sK0)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  fof(f41,plain,(
% 1.58/1.01    ~v2_struct_0(sK0)),
% 1.58/1.01    inference(cnf_transformation,[],[f32])).
% 1.58/1.01  
% 1.58/1.01  cnf(c_17,negated_conjecture,
% 1.58/1.01      ( m1_pre_topc(sK2,sK0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1001,negated_conjecture,
% 1.58/1.01      ( m1_pre_topc(sK2,sK0) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1350,plain,
% 1.58/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_7,plain,
% 1.58/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.58/1.01      | ~ m1_pre_topc(X1,X3)
% 1.58/1.01      | ~ m1_pre_topc(X4,X1)
% 1.58/1.01      | ~ m1_pre_topc(X4,X3)
% 1.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.58/1.01      | ~ v2_pre_topc(X2)
% 1.58/1.01      | ~ v2_pre_topc(X3)
% 1.58/1.01      | v2_struct_0(X3)
% 1.58/1.01      | v2_struct_0(X2)
% 1.58/1.01      | ~ l1_pre_topc(X3)
% 1.58/1.01      | ~ l1_pre_topc(X2)
% 1.58/1.01      | ~ v1_funct_1(X0)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_13,negated_conjecture,
% 1.58/1.01      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 1.58/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_361,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.58/1.01      | ~ m1_pre_topc(X2,X0)
% 1.58/1.01      | ~ m1_pre_topc(X2,X1)
% 1.58/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
% 1.58/1.01      | ~ v2_pre_topc(X4)
% 1.58/1.01      | ~ v2_pre_topc(X1)
% 1.58/1.01      | v2_struct_0(X4)
% 1.58/1.01      | v2_struct_0(X1)
% 1.58/1.01      | ~ l1_pre_topc(X4)
% 1.58/1.01      | ~ l1_pre_topc(X1)
% 1.58/1.01      | ~ v1_funct_1(X3)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
% 1.58/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.58/1.01      | u1_struct_0(X4) != u1_struct_0(sK1)
% 1.58/1.01      | sK4 != X3 ),
% 1.58/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_362,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.58/1.01      | ~ m1_pre_topc(X2,X1)
% 1.58/1.01      | ~ m1_pre_topc(X0,X2)
% 1.58/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
% 1.58/1.01      | ~ v2_pre_topc(X1)
% 1.58/1.01      | ~ v2_pre_topc(X3)
% 1.58/1.01      | v2_struct_0(X1)
% 1.58/1.01      | v2_struct_0(X3)
% 1.58/1.01      | ~ l1_pre_topc(X1)
% 1.58/1.01      | ~ l1_pre_topc(X3)
% 1.58/1.01      | ~ v1_funct_1(sK4)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,X3,X2,X0,sK4)
% 1.58/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.58/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 1.58/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_14,negated_conjecture,
% 1.58/1.01      ( v1_funct_1(sK4) ),
% 1.58/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_366,plain,
% 1.58/1.01      ( ~ l1_pre_topc(X3)
% 1.58/1.01      | ~ l1_pre_topc(X1)
% 1.58/1.01      | v2_struct_0(X3)
% 1.58/1.01      | v2_struct_0(X1)
% 1.58/1.01      | ~ v2_pre_topc(X3)
% 1.58/1.01      | ~ v2_pre_topc(X1)
% 1.58/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
% 1.58/1.01      | ~ m1_pre_topc(X0,X2)
% 1.58/1.01      | ~ m1_pre_topc(X2,X1)
% 1.58/1.01      | ~ m1_pre_topc(X0,X1)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,X3,X2,X0,sK4)
% 1.58/1.01      | u1_struct_0(X2) != u1_struct_0(sK3)
% 1.58/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 1.58/1.01      inference(global_propositional_subsumption,
% 1.58/1.01                [status(thm)],
% 1.58/1.01                [c_362,c_14]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_367,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.58/1.01      | ~ m1_pre_topc(X2,X1)
% 1.58/1.01      | ~ m1_pre_topc(X2,X0)
% 1.58/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 1.58/1.01      | ~ v2_pre_topc(X1)
% 1.58/1.01      | ~ v2_pre_topc(X3)
% 1.58/1.01      | v2_struct_0(X1)
% 1.58/1.01      | v2_struct_0(X3)
% 1.58/1.01      | ~ l1_pre_topc(X1)
% 1.58/1.01      | ~ l1_pre_topc(X3)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 1.58/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.58/1.01      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 1.58/1.01      inference(renaming,[status(thm)],[c_366]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_991,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0_57,X1_57)
% 1.58/1.01      | ~ m1_pre_topc(X2_57,X1_57)
% 1.58/1.01      | ~ m1_pre_topc(X2_57,X0_57)
% 1.58/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X3_57))))
% 1.58/1.01      | ~ v2_pre_topc(X1_57)
% 1.58/1.01      | ~ v2_pre_topc(X3_57)
% 1.58/1.01      | v2_struct_0(X1_57)
% 1.58/1.01      | v2_struct_0(X3_57)
% 1.58/1.01      | ~ l1_pre_topc(X1_57)
% 1.58/1.01      | ~ l1_pre_topc(X3_57)
% 1.58/1.01      | u1_struct_0(X0_57) != u1_struct_0(sK3)
% 1.58/1.01      | u1_struct_0(X3_57) != u1_struct_0(sK1)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X3_57),sK4,u1_struct_0(X2_57)) = k3_tmap_1(X1_57,X3_57,X0_57,X2_57,sK4) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_367]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1360,plain,
% 1.58/1.01      ( u1_struct_0(X0_57) != u1_struct_0(sK3)
% 1.58/1.01      | u1_struct_0(X1_57) != u1_struct_0(sK1)
% 1.58/1.01      | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),sK4,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,sK4)
% 1.58/1.01      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 1.58/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 1.58/1.01      | v2_pre_topc(X3_57) != iProver_top
% 1.58/1.01      | v2_pre_topc(X1_57) != iProver_top
% 1.58/1.01      | v2_struct_0(X3_57) = iProver_top
% 1.58/1.01      | v2_struct_0(X1_57) = iProver_top
% 1.58/1.01      | l1_pre_topc(X3_57) != iProver_top
% 1.58/1.01      | l1_pre_topc(X1_57) != iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1978,plain,
% 1.58/1.01      ( u1_struct_0(X0_57) != u1_struct_0(sK1)
% 1.58/1.01      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_57),sK4,u1_struct_0(X1_57)) = k3_tmap_1(X2_57,X0_57,sK3,X1_57,sK4)
% 1.58/1.01      | m1_pre_topc(X1_57,X2_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X1_57,sK3) != iProver_top
% 1.58/1.01      | m1_pre_topc(sK3,X2_57) != iProver_top
% 1.58/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57)))) != iProver_top
% 1.58/1.01      | v2_pre_topc(X2_57) != iProver_top
% 1.58/1.01      | v2_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | v2_struct_0(X0_57) = iProver_top
% 1.58/1.01      | v2_struct_0(X2_57) = iProver_top
% 1.58/1.01      | l1_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | l1_pre_topc(X2_57) != iProver_top ),
% 1.58/1.01      inference(equality_resolution,[status(thm)],[c_1360]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1995,plain,
% 1.58/1.01      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
% 1.58/1.01      | m1_pre_topc(X0_57,X1_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X0_57,sK3) != iProver_top
% 1.58/1.01      | m1_pre_topc(sK3,X1_57) != iProver_top
% 1.58/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.58/1.01      | v2_pre_topc(X1_57) != iProver_top
% 1.58/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.58/1.01      | v2_struct_0(X1_57) = iProver_top
% 1.58/1.01      | v2_struct_0(sK1) = iProver_top
% 1.58/1.01      | l1_pre_topc(X1_57) != iProver_top
% 1.58/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.58/1.01      inference(equality_resolution,[status(thm)],[c_1978]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_12,negated_conjecture,
% 1.58/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.58/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1004,negated_conjecture,
% 1.58/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1347,plain,
% 1.58/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_2,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.01      | ~ v1_funct_1(X0)
% 1.58/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.58/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_427,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 1.58/1.01      | sK4 != X0 ),
% 1.58/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_14]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_428,plain,
% 1.58/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/1.01      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 1.58/1.01      inference(unflattening,[status(thm)],[c_427]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_990,plain,
% 1.58/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.58/1.01      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_428]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1361,plain,
% 1.58/1.01      ( k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54)
% 1.58/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_990]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1775,plain,
% 1.58/1.01      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 1.58/1.01      inference(superposition,[status(thm)],[c_1347,c_1361]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1996,plain,
% 1.58/1.01      ( k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
% 1.58/1.01      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X1_57,sK3) != iProver_top
% 1.58/1.01      | m1_pre_topc(sK3,X0_57) != iProver_top
% 1.58/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.58/1.01      | v2_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | v2_pre_topc(sK1) != iProver_top
% 1.58/1.01      | v2_struct_0(X0_57) = iProver_top
% 1.58/1.01      | v2_struct_0(sK1) = iProver_top
% 1.58/1.01      | l1_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.58/1.01      inference(demodulation,[status(thm)],[c_1995,c_1775]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_21,negated_conjecture,
% 1.58/1.01      ( ~ v2_struct_0(sK1) ),
% 1.58/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_28,plain,
% 1.58/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_20,negated_conjecture,
% 1.58/1.01      ( v2_pre_topc(sK1) ),
% 1.58/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_29,plain,
% 1.58/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_19,negated_conjecture,
% 1.58/1.01      ( l1_pre_topc(sK1) ),
% 1.58/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_30,plain,
% 1.58/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_37,plain,
% 1.58/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_2058,plain,
% 1.58/1.01      ( l1_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | v2_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
% 1.58/1.01      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X1_57,sK3) != iProver_top
% 1.58/1.01      | m1_pre_topc(sK3,X0_57) != iProver_top
% 1.58/1.01      | v2_struct_0(X0_57) = iProver_top ),
% 1.58/1.01      inference(global_propositional_subsumption,
% 1.58/1.01                [status(thm)],
% 1.58/1.01                [c_1996,c_28,c_29,c_30,c_37]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_2059,plain,
% 1.58/1.01      ( k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
% 1.58/1.01      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 1.58/1.01      | m1_pre_topc(X1_57,sK3) != iProver_top
% 1.58/1.01      | m1_pre_topc(sK3,X0_57) != iProver_top
% 1.58/1.01      | v2_pre_topc(X0_57) != iProver_top
% 1.58/1.01      | v2_struct_0(X0_57) = iProver_top
% 1.58/1.01      | l1_pre_topc(X0_57) != iProver_top ),
% 1.58/1.01      inference(renaming,[status(thm)],[c_2058]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_2073,plain,
% 1.58/1.01      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 1.58/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.58/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.58/1.01      | v2_pre_topc(sK0) != iProver_top
% 1.58/1.01      | v2_struct_0(sK0) = iProver_top
% 1.58/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 1.58/1.01      inference(superposition,[status(thm)],[c_1350,c_2059]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1017,plain,
% 1.58/1.01      ( k1_funct_1(X0_53,X1_53) = k1_funct_1(X2_53,X3_53)
% 1.58/1.01      | X0_53 != X2_53
% 1.58/1.01      | X1_53 != X3_53 ),
% 1.58/1.01      theory(equality) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1857,plain,
% 1.58/1.01      ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
% 1.58/1.01      | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k7_relat_1(sK4,u1_struct_0(sK2))
% 1.58/1.01      | sK5 != sK5 ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1017]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1016,plain,
% 1.58/1.01      ( X0_56 != X1_56 | X2_56 != X1_56 | X2_56 = X0_56 ),
% 1.58/1.01      theory(equality) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1529,plain,
% 1.58/1.01      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_56
% 1.58/1.01      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_56
% 1.58/1.01      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1016]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1753,plain,
% 1.58/1.01      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
% 1.58/1.01      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.58/1.01      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1529]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1550,plain,
% 1.58/1.01      ( X0_56 != X1_56
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X1_56
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_56 ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1016]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1654,plain,
% 1.58/1.01      ( X0_56 != k1_funct_1(sK4,sK5)
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_56
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1550]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1672,plain,
% 1.58/1.01      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5)
% 1.58/1.01      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1654]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_3,plain,
% 1.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.58/1.01      | ~ m1_subset_1(X3,X1)
% 1.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.01      | v1_xboole_0(X1)
% 1.58/1.01      | ~ v1_funct_1(X0)
% 1.58/1.01      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.58/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_340,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,X1)
% 1.58/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.58/1.01      | v1_xboole_0(X1)
% 1.58/1.01      | ~ v1_funct_1(X2)
% 1.58/1.01      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.58/1.01      | u1_struct_0(sK3) != X1
% 1.58/1.01      | u1_struct_0(sK1) != X3
% 1.58/1.01      | sK4 != X2 ),
% 1.58/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_341,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.58/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 1.58/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 1.58/1.01      | ~ v1_funct_1(sK4)
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.58/1.01      inference(unflattening,[status(thm)],[c_340]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_345,plain,
% 1.58/1.01      ( v1_xboole_0(u1_struct_0(sK3))
% 1.58/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.58/1.01      inference(global_propositional_subsumption,
% 1.58/1.01                [status(thm)],
% 1.58/1.01                [c_341,c_14,c_12]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_346,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.58/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.58/1.01      inference(renaming,[status(thm)],[c_345]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_992,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.58/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k1_funct_1(sK4,X0_53) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_346]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1596,plain,
% 1.58/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.58/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 1.58/1.01      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_992]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1010,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1556,plain,
% 1.58/1.01      ( sK5 = sK5 ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1010]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_5,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f38]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1008,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0_57,X1_57)
% 1.58/1.01      | ~ l1_pre_topc(X1_57)
% 1.58/1.01      | l1_pre_topc(X0_57) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1519,plain,
% 1.58/1.01      ( ~ m1_pre_topc(X0_57,sK0)
% 1.58/1.01      | l1_pre_topc(X0_57)
% 1.58/1.01      | ~ l1_pre_topc(sK0) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1008]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1521,plain,
% 1.58/1.01      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_1519]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.01      | v1_relat_1(X0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_0,plain,
% 1.58/1.01      ( ~ r2_hidden(X0,X1)
% 1.58/1.01      | ~ v1_relat_1(X2)
% 1.58/1.01      | ~ v1_funct_1(X2)
% 1.58/1.01      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f33]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_9,negated_conjecture,
% 1.58/1.01      ( r2_hidden(sK5,u1_struct_0(sK2)) ),
% 1.58/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_252,plain,
% 1.58/1.01      ( ~ v1_relat_1(X0)
% 1.58/1.01      | ~ v1_funct_1(X0)
% 1.58/1.01      | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
% 1.58/1.01      | u1_struct_0(sK2) != X1
% 1.58/1.01      | sK5 != X2 ),
% 1.58/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_253,plain,
% 1.58/1.01      ( ~ v1_relat_1(X0)
% 1.58/1.01      | ~ v1_funct_1(X0)
% 1.58/1.01      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5) ),
% 1.58/1.01      inference(unflattening,[status(thm)],[c_252]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_417,plain,
% 1.58/1.01      ( ~ v1_relat_1(X0)
% 1.58/1.01      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5)
% 1.58/1.01      | sK4 != X0 ),
% 1.58/1.01      inference(resolution_lifted,[status(thm)],[c_253,c_14]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_418,plain,
% 1.58/1.01      ( ~ v1_relat_1(sK4)
% 1.58/1.01      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(unflattening,[status(thm)],[c_417]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_445,plain,
% 1.58/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.58/1.01      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)
% 1.58/1.01      | sK4 != X0 ),
% 1.58/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_418]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_446,plain,
% 1.58/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.58/1.01      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(unflattening,[status(thm)],[c_445]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_989,plain,
% 1.58/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 1.58/1.01      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_446]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1501,plain,
% 1.58/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 1.58/1.01      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_989]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_8,negated_conjecture,
% 1.58/1.01      ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.58/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_1007,negated_conjecture,
% 1.58/1.01      ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.58/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_4,plain,
% 1.58/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_6,plain,
% 1.58/1.01      ( v2_struct_0(X0)
% 1.58/1.01      | ~ l1_struct_0(X0)
% 1.58/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.58/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_288,plain,
% 1.58/1.01      ( v2_struct_0(X0)
% 1.58/1.01      | ~ l1_pre_topc(X0)
% 1.58/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.58/1.01      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_290,plain,
% 1.58/1.01      ( v2_struct_0(sK3)
% 1.58/1.01      | ~ l1_pre_topc(sK3)
% 1.58/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.58/1.01      inference(instantiation,[status(thm)],[c_288]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_10,negated_conjecture,
% 1.58/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.58/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_11,negated_conjecture,
% 1.58/1.01      ( m1_pre_topc(sK2,sK3) ),
% 1.58/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_38,plain,
% 1.58/1.01      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_15,negated_conjecture,
% 1.58/1.01      ( m1_pre_topc(sK3,sK0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_34,plain,
% 1.58/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_16,negated_conjecture,
% 1.58/1.01      ( ~ v2_struct_0(sK3) ),
% 1.58/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_22,negated_conjecture,
% 1.58/1.01      ( l1_pre_topc(sK0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_27,plain,
% 1.58/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_23,negated_conjecture,
% 1.58/1.01      ( v2_pre_topc(sK0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_26,plain,
% 1.58/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_24,negated_conjecture,
% 1.58/1.01      ( ~ v2_struct_0(sK0) ),
% 1.58/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(c_25,plain,
% 1.58/1.01      ( v2_struct_0(sK0) != iProver_top ),
% 1.58/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.58/1.01  
% 1.58/1.01  cnf(contradiction,plain,
% 1.58/1.01      ( $false ),
% 1.58/1.01      inference(minisat,
% 1.58/1.01                [status(thm)],
% 1.58/1.01                [c_2073,c_1857,c_1753,c_1672,c_1596,c_1556,c_1521,c_1501,
% 1.58/1.01                 c_1007,c_290,c_10,c_38,c_12,c_34,c_15,c_16,c_27,c_22,
% 1.58/1.01                 c_26,c_25]) ).
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.58/1.01  
% 1.58/1.01  ------                               Statistics
% 1.58/1.01  
% 1.58/1.01  ------ General
% 1.58/1.01  
% 1.58/1.01  abstr_ref_over_cycles:                  0
% 1.58/1.01  abstr_ref_under_cycles:                 0
% 1.58/1.01  gc_basic_clause_elim:                   0
% 1.58/1.01  forced_gc_time:                         0
% 1.58/1.01  parsing_time:                           0.008
% 1.58/1.01  unif_index_cands_time:                  0.
% 1.58/1.01  unif_index_add_time:                    0.
% 1.58/1.01  orderings_time:                         0.
% 1.58/1.01  out_proof_time:                         0.011
% 1.58/1.01  total_time:                             0.102
% 1.58/1.01  num_of_symbols:                         58
% 1.58/1.01  num_of_terms:                           1826
% 1.58/1.01  
% 1.58/1.01  ------ Preprocessing
% 1.58/1.01  
% 1.58/1.01  num_of_splits:                          0
% 1.58/1.01  num_of_split_atoms:                     0
% 1.58/1.01  num_of_reused_defs:                     0
% 1.58/1.01  num_eq_ax_congr_red:                    15
% 1.58/1.01  num_of_sem_filtered_clauses:            1
% 1.58/1.01  num_of_subtypes:                        5
% 1.58/1.01  monotx_restored_types:                  0
% 1.58/1.01  sat_num_of_epr_types:                   0
% 1.58/1.01  sat_num_of_non_cyclic_types:            0
% 1.58/1.01  sat_guarded_non_collapsed_types:        0
% 1.58/1.01  num_pure_diseq_elim:                    0
% 1.58/1.01  simp_replaced_by:                       0
% 1.58/1.01  res_preprocessed:                       118
% 1.58/1.01  prep_upred:                             0
% 1.58/1.01  prep_unflattend:                        14
% 1.58/1.01  smt_new_axioms:                         0
% 1.58/1.01  pred_elim_cands:                        6
% 1.58/1.01  pred_elim:                              5
% 1.58/1.01  pred_elim_cl:                           5
% 1.58/1.01  pred_elim_cycles:                       11
% 1.58/1.01  merged_defs:                            0
% 1.58/1.01  merged_defs_ncl:                        0
% 1.58/1.01  bin_hyper_res:                          0
% 1.58/1.01  prep_cycles:                            4
% 1.58/1.01  pred_elim_time:                         0.015
% 1.58/1.01  splitting_time:                         0.
% 1.58/1.01  sem_filter_time:                        0.
% 1.58/1.01  monotx_time:                            0.
% 1.58/1.01  subtype_inf_time:                       0.
% 1.58/1.01  
% 1.58/1.01  ------ Problem properties
% 1.58/1.01  
% 1.58/1.01  clauses:                                20
% 1.58/1.01  conjectures:                            14
% 1.58/1.01  epr:                                    12
% 1.58/1.01  horn:                                   18
% 1.58/1.01  ground:                                 14
% 1.58/1.01  unary:                                  14
% 1.58/1.01  binary:                                 2
% 1.58/1.01  lits:                                   40
% 1.58/1.01  lits_eq:                                7
% 1.58/1.01  fd_pure:                                0
% 1.58/1.01  fd_pseudo:                              0
% 1.58/1.01  fd_cond:                                0
% 1.58/1.01  fd_pseudo_cond:                         0
% 1.58/1.01  ac_symbols:                             0
% 1.58/1.01  
% 1.58/1.01  ------ Propositional Solver
% 1.58/1.01  
% 1.58/1.01  prop_solver_calls:                      29
% 1.58/1.01  prop_fast_solver_calls:                 759
% 1.58/1.01  smt_solver_calls:                       0
% 1.58/1.01  smt_fast_solver_calls:                  0
% 1.58/1.01  prop_num_of_clauses:                    438
% 1.58/1.01  prop_preprocess_simplified:             2681
% 1.58/1.01  prop_fo_subsumed:                       11
% 1.58/1.01  prop_solver_time:                       0.
% 1.58/1.01  smt_solver_time:                        0.
% 1.58/1.01  smt_fast_solver_time:                   0.
% 1.58/1.01  prop_fast_solver_time:                  0.
% 1.58/1.01  prop_unsat_core_time:                   0.
% 1.58/1.01  
% 1.58/1.01  ------ QBF
% 1.58/1.01  
% 1.58/1.01  qbf_q_res:                              0
% 1.58/1.01  qbf_num_tautologies:                    0
% 1.58/1.01  qbf_prep_cycles:                        0
% 1.58/1.01  
% 1.58/1.01  ------ BMC1
% 1.58/1.01  
% 1.58/1.01  bmc1_current_bound:                     -1
% 1.58/1.01  bmc1_last_solved_bound:                 -1
% 1.58/1.01  bmc1_unsat_core_size:                   -1
% 1.58/1.01  bmc1_unsat_core_parents_size:           -1
% 1.58/1.01  bmc1_merge_next_fun:                    0
% 1.58/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.58/1.01  
% 1.58/1.01  ------ Instantiation
% 1.58/1.01  
% 1.58/1.01  inst_num_of_clauses:                    158
% 1.58/1.01  inst_num_in_passive:                    27
% 1.58/1.01  inst_num_in_active:                     128
% 1.58/1.01  inst_num_in_unprocessed:                3
% 1.58/1.01  inst_num_of_loops:                      140
% 1.58/1.01  inst_num_of_learning_restarts:          0
% 1.58/1.01  inst_num_moves_active_passive:          7
% 1.58/1.01  inst_lit_activity:                      0
% 1.58/1.01  inst_lit_activity_moves:                0
% 1.58/1.01  inst_num_tautologies:                   0
% 1.58/1.01  inst_num_prop_implied:                  0
% 1.58/1.01  inst_num_existing_simplified:           0
% 1.58/1.01  inst_num_eq_res_simplified:             0
% 1.58/1.01  inst_num_child_elim:                    0
% 1.58/1.01  inst_num_of_dismatching_blockings:      13
% 1.58/1.01  inst_num_of_non_proper_insts:           153
% 1.58/1.01  inst_num_of_duplicates:                 0
% 1.58/1.01  inst_inst_num_from_inst_to_res:         0
% 1.58/1.01  inst_dismatching_checking_time:         0.
% 1.58/1.01  
% 1.58/1.01  ------ Resolution
% 1.58/1.01  
% 1.58/1.01  res_num_of_clauses:                     0
% 1.58/1.01  res_num_in_passive:                     0
% 1.58/1.01  res_num_in_active:                      0
% 1.58/1.01  res_num_of_loops:                       122
% 1.58/1.01  res_forward_subset_subsumed:            48
% 1.58/1.01  res_backward_subset_subsumed:           0
% 1.58/1.01  res_forward_subsumed:                   0
% 1.58/1.01  res_backward_subsumed:                  0
% 1.58/1.01  res_forward_subsumption_resolution:     0
% 1.58/1.01  res_backward_subsumption_resolution:    0
% 1.58/1.01  res_clause_to_clause_subsumption:       59
% 1.58/1.01  res_orphan_elimination:                 0
% 1.58/1.01  res_tautology_del:                      25
% 1.58/1.01  res_num_eq_res_simplified:              0
% 1.58/1.01  res_num_sel_changes:                    0
% 1.58/1.01  res_moves_from_active_to_pass:          0
% 1.58/1.01  
% 1.58/1.01  ------ Superposition
% 1.58/1.01  
% 1.58/1.01  sup_time_total:                         0.
% 1.58/1.01  sup_time_generating:                    0.
% 1.58/1.01  sup_time_sim_full:                      0.
% 1.58/1.01  sup_time_sim_immed:                     0.
% 1.58/1.01  
% 1.58/1.01  sup_num_of_clauses:                     29
% 1.58/1.01  sup_num_in_active:                      26
% 1.58/1.01  sup_num_in_passive:                     3
% 1.58/1.01  sup_num_of_loops:                       26
% 1.58/1.01  sup_fw_superposition:                   7
% 1.58/1.01  sup_bw_superposition:                   1
% 1.58/1.01  sup_immediate_simplified:               1
% 1.58/1.01  sup_given_eliminated:                   0
% 1.58/1.01  comparisons_done:                       0
% 1.58/1.01  comparisons_avoided:                    0
% 1.58/1.01  
% 1.58/1.01  ------ Simplifications
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  sim_fw_subset_subsumed:                 0
% 1.58/1.01  sim_bw_subset_subsumed:                 1
% 1.58/1.01  sim_fw_subsumed:                        0
% 1.58/1.01  sim_bw_subsumed:                        0
% 1.58/1.01  sim_fw_subsumption_res:                 0
% 1.58/1.01  sim_bw_subsumption_res:                 0
% 1.58/1.01  sim_tautology_del:                      0
% 1.58/1.01  sim_eq_tautology_del:                   0
% 1.58/1.01  sim_eq_res_simp:                        0
% 1.58/1.01  sim_fw_demodulated:                     1
% 1.58/1.01  sim_bw_demodulated:                     1
% 1.58/1.01  sim_light_normalised:                   0
% 1.58/1.01  sim_joinable_taut:                      0
% 1.58/1.01  sim_joinable_simp:                      0
% 1.58/1.01  sim_ac_normalised:                      0
% 1.58/1.01  sim_smt_subsumption:                    0
% 1.58/1.01  
%------------------------------------------------------------------------------
