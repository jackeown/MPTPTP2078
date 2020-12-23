%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:49 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 439 expanded)
%              Number of clauses        :   87 (  99 expanded)
%              Number of leaves         :   18 ( 194 expanded)
%              Depth                    :   19
%              Number of atoms          :  675 (5875 expanded)
%              Number of equality atoms :  192 ( 620 expanded)
%              Maximal formula depth    :   19 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),sK5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK5)
        & r2_hidden(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f30,f29,f28,f27,f26,f25])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f38,plain,(
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

fof(f51,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_617,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_948,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_375,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_376,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_380,plain,
    ( ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_14])).

cnf(c_381,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X3) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_608,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X3_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X3_54),sK4,u1_struct_0(X2_54)) = k3_tmap_1(X1_54,X3_54,X0_54,X2_54,sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | u1_struct_0(X3_54) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_957,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_1620,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_54),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK3,X1_54,sK4)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X2_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_957])).

cnf(c_1637,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1620])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_620,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_945,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_607,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_partfun1(X0_52,X1_52,sK4,X2_52) = k7_relat_1(sK4,X2_52) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_958,plain,
    ( k2_partfun1(X0_52,X1_52,sK4,X2_52) = k7_relat_1(sK4,X2_52)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_1417,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_52) = k7_relat_1(sK4,X0_52) ),
    inference(superposition,[status(thm)],[c_945,c_958])).

cnf(c_1638,plain,
    ( k3_tmap_1(X0_54,sK1,sK3,X1_54,sK4) = k7_relat_1(sK4,u1_struct_0(X1_54))
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1637,c_1417])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1696,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | k3_tmap_1(X0_54,sK1,sK3,X1_54,sK4) = k7_relat_1(sK4,u1_struct_0(X1_54))
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_28,c_29,c_30,c_37])).

cnf(c_1697,plain,
    ( k3_tmap_1(X0_54,sK1,sK3,X1_54,sK4) = k7_relat_1(sK4,u1_struct_0(X1_54))
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_1696])).

cnf(c_1711,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_1697])).

cnf(c_633,plain,
    ( k1_funct_1(X0_52,X1_52) = k1_funct_1(X2_52,X3_52)
    | X0_52 != X2_52
    | X1_52 != X3_52 ),
    theory(equality)).

cnf(c_1567,plain,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k7_relat_1(sK4,u1_struct_0(sK2))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_630,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1124,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_53
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_53
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1485,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1146,plain,
    ( X0_53 != X1_53
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X1_53
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1276,plain,
    ( X0_53 != k1_funct_1(sK4,sK5)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_1343,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5)
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | u1_struct_0(sK2) != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_288,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_323,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X4))
    | ~ v1_funct_1(X0)
    | X1 != X4
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution_lifted,[status(thm)],[c_288,c_4])).

cnf(c_324,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X1))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK1) != X3
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_13])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_14,c_12])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_52) = k1_funct_1(sK4,X0_52) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_624,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1196,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_627,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1156,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_625,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1109,plain,
    ( ~ m1_pre_topc(X0_54,sK0)
    | l1_pre_topc(X0_54)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1111,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_272,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_273,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_431,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_14])).

cnf(c_432,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_432])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_606,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_460])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_8,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_623,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1711,c_1567,c_1485,c_1343,c_1206,c_1196,c_1156,c_1111,c_1097,c_623,c_10,c_38,c_11,c_12,c_34,c_15,c_27,c_22,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.49/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.00  
% 1.49/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.49/1.00  
% 1.49/1.00  ------  iProver source info
% 1.49/1.00  
% 1.49/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.49/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.49/1.00  git: non_committed_changes: false
% 1.49/1.00  git: last_make_outside_of_git: false
% 1.49/1.00  
% 1.49/1.00  ------ 
% 1.49/1.00  
% 1.49/1.00  ------ Input Options
% 1.49/1.00  
% 1.49/1.00  --out_options                           all
% 1.49/1.00  --tptp_safe_out                         true
% 1.49/1.00  --problem_path                          ""
% 1.49/1.00  --include_path                          ""
% 1.49/1.00  --clausifier                            res/vclausify_rel
% 1.49/1.00  --clausifier_options                    --mode clausify
% 1.49/1.00  --stdin                                 false
% 1.49/1.00  --stats_out                             all
% 1.49/1.00  
% 1.49/1.00  ------ General Options
% 1.49/1.00  
% 1.49/1.00  --fof                                   false
% 1.49/1.00  --time_out_real                         305.
% 1.49/1.00  --time_out_virtual                      -1.
% 1.49/1.00  --symbol_type_check                     false
% 1.49/1.00  --clausify_out                          false
% 1.49/1.00  --sig_cnt_out                           false
% 1.49/1.00  --trig_cnt_out                          false
% 1.49/1.00  --trig_cnt_out_tolerance                1.
% 1.49/1.00  --trig_cnt_out_sk_spl                   false
% 1.49/1.00  --abstr_cl_out                          false
% 1.49/1.00  
% 1.49/1.00  ------ Global Options
% 1.49/1.00  
% 1.49/1.00  --schedule                              default
% 1.49/1.00  --add_important_lit                     false
% 1.49/1.00  --prop_solver_per_cl                    1000
% 1.49/1.00  --min_unsat_core                        false
% 1.49/1.00  --soft_assumptions                      false
% 1.49/1.00  --soft_lemma_size                       3
% 1.49/1.00  --prop_impl_unit_size                   0
% 1.49/1.00  --prop_impl_unit                        []
% 1.49/1.00  --share_sel_clauses                     true
% 1.49/1.00  --reset_solvers                         false
% 1.49/1.00  --bc_imp_inh                            [conj_cone]
% 1.49/1.00  --conj_cone_tolerance                   3.
% 1.49/1.00  --extra_neg_conj                        none
% 1.49/1.00  --large_theory_mode                     true
% 1.49/1.00  --prolific_symb_bound                   200
% 1.49/1.00  --lt_threshold                          2000
% 1.49/1.00  --clause_weak_htbl                      true
% 1.49/1.00  --gc_record_bc_elim                     false
% 1.49/1.00  
% 1.49/1.00  ------ Preprocessing Options
% 1.49/1.00  
% 1.49/1.00  --preprocessing_flag                    true
% 1.49/1.00  --time_out_prep_mult                    0.1
% 1.49/1.00  --splitting_mode                        input
% 1.49/1.00  --splitting_grd                         true
% 1.49/1.00  --splitting_cvd                         false
% 1.49/1.00  --splitting_cvd_svl                     false
% 1.49/1.00  --splitting_nvd                         32
% 1.49/1.00  --sub_typing                            true
% 1.49/1.00  --prep_gs_sim                           true
% 1.49/1.00  --prep_unflatten                        true
% 1.49/1.00  --prep_res_sim                          true
% 1.49/1.00  --prep_upred                            true
% 1.49/1.00  --prep_sem_filter                       exhaustive
% 1.49/1.00  --prep_sem_filter_out                   false
% 1.49/1.00  --pred_elim                             true
% 1.49/1.00  --res_sim_input                         true
% 1.49/1.00  --eq_ax_congr_red                       true
% 1.49/1.00  --pure_diseq_elim                       true
% 1.49/1.00  --brand_transform                       false
% 1.49/1.00  --non_eq_to_eq                          false
% 1.49/1.00  --prep_def_merge                        true
% 1.49/1.00  --prep_def_merge_prop_impl              false
% 1.49/1.00  --prep_def_merge_mbd                    true
% 1.49/1.00  --prep_def_merge_tr_red                 false
% 1.49/1.00  --prep_def_merge_tr_cl                  false
% 1.49/1.00  --smt_preprocessing                     true
% 1.49/1.00  --smt_ac_axioms                         fast
% 1.49/1.00  --preprocessed_out                      false
% 1.49/1.00  --preprocessed_stats                    false
% 1.49/1.00  
% 1.49/1.00  ------ Abstraction refinement Options
% 1.49/1.00  
% 1.49/1.00  --abstr_ref                             []
% 1.49/1.00  --abstr_ref_prep                        false
% 1.49/1.00  --abstr_ref_until_sat                   false
% 1.49/1.00  --abstr_ref_sig_restrict                funpre
% 1.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.49/1.00  --abstr_ref_under                       []
% 1.49/1.00  
% 1.49/1.00  ------ SAT Options
% 1.49/1.00  
% 1.49/1.00  --sat_mode                              false
% 1.49/1.00  --sat_fm_restart_options                ""
% 1.49/1.00  --sat_gr_def                            false
% 1.49/1.00  --sat_epr_types                         true
% 1.49/1.00  --sat_non_cyclic_types                  false
% 1.49/1.00  --sat_finite_models                     false
% 1.49/1.00  --sat_fm_lemmas                         false
% 1.49/1.00  --sat_fm_prep                           false
% 1.49/1.00  --sat_fm_uc_incr                        true
% 1.49/1.00  --sat_out_model                         small
% 1.49/1.00  --sat_out_clauses                       false
% 1.49/1.00  
% 1.49/1.00  ------ QBF Options
% 1.49/1.00  
% 1.49/1.00  --qbf_mode                              false
% 1.49/1.00  --qbf_elim_univ                         false
% 1.49/1.00  --qbf_dom_inst                          none
% 1.49/1.00  --qbf_dom_pre_inst                      false
% 1.49/1.00  --qbf_sk_in                             false
% 1.49/1.00  --qbf_pred_elim                         true
% 1.49/1.00  --qbf_split                             512
% 1.49/1.00  
% 1.49/1.00  ------ BMC1 Options
% 1.49/1.00  
% 1.49/1.00  --bmc1_incremental                      false
% 1.49/1.00  --bmc1_axioms                           reachable_all
% 1.49/1.00  --bmc1_min_bound                        0
% 1.49/1.00  --bmc1_max_bound                        -1
% 1.49/1.00  --bmc1_max_bound_default                -1
% 1.49/1.00  --bmc1_symbol_reachability              true
% 1.49/1.00  --bmc1_property_lemmas                  false
% 1.49/1.00  --bmc1_k_induction                      false
% 1.49/1.00  --bmc1_non_equiv_states                 false
% 1.49/1.00  --bmc1_deadlock                         false
% 1.49/1.00  --bmc1_ucm                              false
% 1.49/1.00  --bmc1_add_unsat_core                   none
% 1.49/1.00  --bmc1_unsat_core_children              false
% 1.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.49/1.00  --bmc1_out_stat                         full
% 1.49/1.00  --bmc1_ground_init                      false
% 1.49/1.00  --bmc1_pre_inst_next_state              false
% 1.49/1.00  --bmc1_pre_inst_state                   false
% 1.49/1.00  --bmc1_pre_inst_reach_state             false
% 1.49/1.00  --bmc1_out_unsat_core                   false
% 1.49/1.00  --bmc1_aig_witness_out                  false
% 1.49/1.00  --bmc1_verbose                          false
% 1.49/1.00  --bmc1_dump_clauses_tptp                false
% 1.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.49/1.00  --bmc1_dump_file                        -
% 1.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.49/1.00  --bmc1_ucm_extend_mode                  1
% 1.49/1.00  --bmc1_ucm_init_mode                    2
% 1.49/1.00  --bmc1_ucm_cone_mode                    none
% 1.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.49/1.00  --bmc1_ucm_relax_model                  4
% 1.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.49/1.00  --bmc1_ucm_layered_model                none
% 1.49/1.00  --bmc1_ucm_max_lemma_size               10
% 1.49/1.00  
% 1.49/1.00  ------ AIG Options
% 1.49/1.00  
% 1.49/1.00  --aig_mode                              false
% 1.49/1.00  
% 1.49/1.00  ------ Instantiation Options
% 1.49/1.00  
% 1.49/1.00  --instantiation_flag                    true
% 1.49/1.00  --inst_sos_flag                         false
% 1.49/1.00  --inst_sos_phase                        true
% 1.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.49/1.00  --inst_lit_sel_side                     num_symb
% 1.49/1.00  --inst_solver_per_active                1400
% 1.49/1.00  --inst_solver_calls_frac                1.
% 1.49/1.00  --inst_passive_queue_type               priority_queues
% 1.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.49/1.00  --inst_passive_queues_freq              [25;2]
% 1.49/1.00  --inst_dismatching                      true
% 1.49/1.00  --inst_eager_unprocessed_to_passive     true
% 1.49/1.00  --inst_prop_sim_given                   true
% 1.49/1.00  --inst_prop_sim_new                     false
% 1.49/1.00  --inst_subs_new                         false
% 1.49/1.00  --inst_eq_res_simp                      false
% 1.49/1.00  --inst_subs_given                       false
% 1.49/1.00  --inst_orphan_elimination               true
% 1.49/1.00  --inst_learning_loop_flag               true
% 1.49/1.00  --inst_learning_start                   3000
% 1.49/1.00  --inst_learning_factor                  2
% 1.49/1.00  --inst_start_prop_sim_after_learn       3
% 1.49/1.00  --inst_sel_renew                        solver
% 1.49/1.00  --inst_lit_activity_flag                true
% 1.49/1.00  --inst_restr_to_given                   false
% 1.49/1.00  --inst_activity_threshold               500
% 1.49/1.00  --inst_out_proof                        true
% 1.49/1.00  
% 1.49/1.00  ------ Resolution Options
% 1.49/1.00  
% 1.49/1.00  --resolution_flag                       true
% 1.49/1.00  --res_lit_sel                           adaptive
% 1.49/1.00  --res_lit_sel_side                      none
% 1.49/1.00  --res_ordering                          kbo
% 1.49/1.00  --res_to_prop_solver                    active
% 1.49/1.00  --res_prop_simpl_new                    false
% 1.49/1.00  --res_prop_simpl_given                  true
% 1.49/1.00  --res_passive_queue_type                priority_queues
% 1.49/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.49/1.00  --res_passive_queues_freq               [15;5]
% 1.49/1.00  --res_forward_subs                      full
% 1.49/1.00  --res_backward_subs                     full
% 1.49/1.00  --res_forward_subs_resolution           true
% 1.49/1.00  --res_backward_subs_resolution          true
% 1.49/1.00  --res_orphan_elimination                true
% 1.49/1.00  --res_time_limit                        2.
% 1.49/1.00  --res_out_proof                         true
% 1.49/1.00  
% 1.49/1.00  ------ Superposition Options
% 1.49/1.00  
% 1.49/1.00  --superposition_flag                    true
% 1.49/1.00  --sup_passive_queue_type                priority_queues
% 1.49/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.49/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.49/1.00  --demod_completeness_check              fast
% 1.49/1.00  --demod_use_ground                      true
% 1.49/1.00  --sup_to_prop_solver                    passive
% 1.49/1.00  --sup_prop_simpl_new                    true
% 1.49/1.00  --sup_prop_simpl_given                  true
% 1.49/1.00  --sup_fun_splitting                     false
% 1.49/1.00  --sup_smt_interval                      50000
% 1.49/1.00  
% 1.49/1.00  ------ Superposition Simplification Setup
% 1.49/1.00  
% 1.49/1.00  --sup_indices_passive                   []
% 1.49/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.49/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.00  --sup_full_bw                           [BwDemod]
% 1.49/1.00  --sup_immed_triv                        [TrivRules]
% 1.49/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.49/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.00  --sup_immed_bw_main                     []
% 1.49/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.49/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.49/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.49/1.00  
% 1.49/1.00  ------ Combination Options
% 1.49/1.00  
% 1.49/1.00  --comb_res_mult                         3
% 1.49/1.00  --comb_sup_mult                         2
% 1.49/1.00  --comb_inst_mult                        10
% 1.49/1.00  
% 1.49/1.00  ------ Debug Options
% 1.49/1.00  
% 1.49/1.00  --dbg_backtrace                         false
% 1.49/1.00  --dbg_dump_prop_clauses                 false
% 1.49/1.00  --dbg_dump_prop_clauses_file            -
% 1.49/1.00  --dbg_out_stat                          false
% 1.49/1.00  ------ Parsing...
% 1.49/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.49/1.00  
% 1.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.49/1.00  
% 1.49/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.49/1.00  
% 1.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.49/1.00  ------ Proving...
% 1.49/1.00  ------ Problem Properties 
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  clauses                                 20
% 1.49/1.00  conjectures                             14
% 1.49/1.00  EPR                                     12
% 1.49/1.00  Horn                                    19
% 1.49/1.00  unary                                   14
% 1.49/1.00  binary                                  2
% 1.49/1.00  lits                                    40
% 1.49/1.00  lits eq                                 7
% 1.49/1.00  fd_pure                                 0
% 1.49/1.00  fd_pseudo                               0
% 1.49/1.00  fd_cond                                 0
% 1.49/1.00  fd_pseudo_cond                          0
% 1.49/1.00  AC symbols                              0
% 1.49/1.00  
% 1.49/1.00  ------ Schedule dynamic 5 is on 
% 1.49/1.00  
% 1.49/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  ------ 
% 1.49/1.00  Current options:
% 1.49/1.00  ------ 
% 1.49/1.00  
% 1.49/1.00  ------ Input Options
% 1.49/1.00  
% 1.49/1.00  --out_options                           all
% 1.49/1.00  --tptp_safe_out                         true
% 1.49/1.00  --problem_path                          ""
% 1.49/1.00  --include_path                          ""
% 1.49/1.00  --clausifier                            res/vclausify_rel
% 1.49/1.00  --clausifier_options                    --mode clausify
% 1.49/1.00  --stdin                                 false
% 1.49/1.00  --stats_out                             all
% 1.49/1.00  
% 1.49/1.00  ------ General Options
% 1.49/1.00  
% 1.49/1.00  --fof                                   false
% 1.49/1.00  --time_out_real                         305.
% 1.49/1.00  --time_out_virtual                      -1.
% 1.49/1.00  --symbol_type_check                     false
% 1.49/1.00  --clausify_out                          false
% 1.49/1.00  --sig_cnt_out                           false
% 1.49/1.00  --trig_cnt_out                          false
% 1.49/1.00  --trig_cnt_out_tolerance                1.
% 1.49/1.00  --trig_cnt_out_sk_spl                   false
% 1.49/1.00  --abstr_cl_out                          false
% 1.49/1.00  
% 1.49/1.00  ------ Global Options
% 1.49/1.00  
% 1.49/1.00  --schedule                              default
% 1.49/1.00  --add_important_lit                     false
% 1.49/1.00  --prop_solver_per_cl                    1000
% 1.49/1.00  --min_unsat_core                        false
% 1.49/1.00  --soft_assumptions                      false
% 1.49/1.00  --soft_lemma_size                       3
% 1.49/1.00  --prop_impl_unit_size                   0
% 1.49/1.00  --prop_impl_unit                        []
% 1.49/1.00  --share_sel_clauses                     true
% 1.49/1.00  --reset_solvers                         false
% 1.49/1.00  --bc_imp_inh                            [conj_cone]
% 1.49/1.00  --conj_cone_tolerance                   3.
% 1.49/1.00  --extra_neg_conj                        none
% 1.49/1.00  --large_theory_mode                     true
% 1.49/1.00  --prolific_symb_bound                   200
% 1.49/1.00  --lt_threshold                          2000
% 1.49/1.00  --clause_weak_htbl                      true
% 1.49/1.00  --gc_record_bc_elim                     false
% 1.49/1.00  
% 1.49/1.00  ------ Preprocessing Options
% 1.49/1.00  
% 1.49/1.00  --preprocessing_flag                    true
% 1.49/1.00  --time_out_prep_mult                    0.1
% 1.49/1.00  --splitting_mode                        input
% 1.49/1.00  --splitting_grd                         true
% 1.49/1.00  --splitting_cvd                         false
% 1.49/1.00  --splitting_cvd_svl                     false
% 1.49/1.00  --splitting_nvd                         32
% 1.49/1.00  --sub_typing                            true
% 1.49/1.00  --prep_gs_sim                           true
% 1.49/1.00  --prep_unflatten                        true
% 1.49/1.00  --prep_res_sim                          true
% 1.49/1.00  --prep_upred                            true
% 1.49/1.00  --prep_sem_filter                       exhaustive
% 1.49/1.00  --prep_sem_filter_out                   false
% 1.49/1.00  --pred_elim                             true
% 1.49/1.00  --res_sim_input                         true
% 1.49/1.00  --eq_ax_congr_red                       true
% 1.49/1.00  --pure_diseq_elim                       true
% 1.49/1.00  --brand_transform                       false
% 1.49/1.00  --non_eq_to_eq                          false
% 1.49/1.00  --prep_def_merge                        true
% 1.49/1.00  --prep_def_merge_prop_impl              false
% 1.49/1.00  --prep_def_merge_mbd                    true
% 1.49/1.00  --prep_def_merge_tr_red                 false
% 1.49/1.00  --prep_def_merge_tr_cl                  false
% 1.49/1.00  --smt_preprocessing                     true
% 1.49/1.00  --smt_ac_axioms                         fast
% 1.49/1.00  --preprocessed_out                      false
% 1.49/1.00  --preprocessed_stats                    false
% 1.49/1.00  
% 1.49/1.00  ------ Abstraction refinement Options
% 1.49/1.00  
% 1.49/1.00  --abstr_ref                             []
% 1.49/1.00  --abstr_ref_prep                        false
% 1.49/1.00  --abstr_ref_until_sat                   false
% 1.49/1.00  --abstr_ref_sig_restrict                funpre
% 1.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.49/1.00  --abstr_ref_under                       []
% 1.49/1.00  
% 1.49/1.00  ------ SAT Options
% 1.49/1.00  
% 1.49/1.00  --sat_mode                              false
% 1.49/1.00  --sat_fm_restart_options                ""
% 1.49/1.00  --sat_gr_def                            false
% 1.49/1.00  --sat_epr_types                         true
% 1.49/1.00  --sat_non_cyclic_types                  false
% 1.49/1.00  --sat_finite_models                     false
% 1.49/1.00  --sat_fm_lemmas                         false
% 1.49/1.00  --sat_fm_prep                           false
% 1.49/1.00  --sat_fm_uc_incr                        true
% 1.49/1.00  --sat_out_model                         small
% 1.49/1.00  --sat_out_clauses                       false
% 1.49/1.00  
% 1.49/1.00  ------ QBF Options
% 1.49/1.00  
% 1.49/1.00  --qbf_mode                              false
% 1.49/1.00  --qbf_elim_univ                         false
% 1.49/1.00  --qbf_dom_inst                          none
% 1.49/1.00  --qbf_dom_pre_inst                      false
% 1.49/1.00  --qbf_sk_in                             false
% 1.49/1.00  --qbf_pred_elim                         true
% 1.49/1.00  --qbf_split                             512
% 1.49/1.00  
% 1.49/1.00  ------ BMC1 Options
% 1.49/1.00  
% 1.49/1.00  --bmc1_incremental                      false
% 1.49/1.00  --bmc1_axioms                           reachable_all
% 1.49/1.00  --bmc1_min_bound                        0
% 1.49/1.00  --bmc1_max_bound                        -1
% 1.49/1.00  --bmc1_max_bound_default                -1
% 1.49/1.00  --bmc1_symbol_reachability              true
% 1.49/1.00  --bmc1_property_lemmas                  false
% 1.49/1.00  --bmc1_k_induction                      false
% 1.49/1.00  --bmc1_non_equiv_states                 false
% 1.49/1.00  --bmc1_deadlock                         false
% 1.49/1.00  --bmc1_ucm                              false
% 1.49/1.00  --bmc1_add_unsat_core                   none
% 1.49/1.00  --bmc1_unsat_core_children              false
% 1.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.49/1.00  --bmc1_out_stat                         full
% 1.49/1.00  --bmc1_ground_init                      false
% 1.49/1.00  --bmc1_pre_inst_next_state              false
% 1.49/1.00  --bmc1_pre_inst_state                   false
% 1.49/1.00  --bmc1_pre_inst_reach_state             false
% 1.49/1.00  --bmc1_out_unsat_core                   false
% 1.49/1.00  --bmc1_aig_witness_out                  false
% 1.49/1.00  --bmc1_verbose                          false
% 1.49/1.00  --bmc1_dump_clauses_tptp                false
% 1.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.49/1.00  --bmc1_dump_file                        -
% 1.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.49/1.00  --bmc1_ucm_extend_mode                  1
% 1.49/1.00  --bmc1_ucm_init_mode                    2
% 1.49/1.00  --bmc1_ucm_cone_mode                    none
% 1.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.49/1.00  --bmc1_ucm_relax_model                  4
% 1.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.49/1.00  --bmc1_ucm_layered_model                none
% 1.49/1.00  --bmc1_ucm_max_lemma_size               10
% 1.49/1.00  
% 1.49/1.00  ------ AIG Options
% 1.49/1.00  
% 1.49/1.00  --aig_mode                              false
% 1.49/1.00  
% 1.49/1.00  ------ Instantiation Options
% 1.49/1.00  
% 1.49/1.00  --instantiation_flag                    true
% 1.49/1.00  --inst_sos_flag                         false
% 1.49/1.00  --inst_sos_phase                        true
% 1.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.49/1.00  --inst_lit_sel_side                     none
% 1.49/1.00  --inst_solver_per_active                1400
% 1.49/1.00  --inst_solver_calls_frac                1.
% 1.49/1.00  --inst_passive_queue_type               priority_queues
% 1.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.49/1.00  --inst_passive_queues_freq              [25;2]
% 1.49/1.00  --inst_dismatching                      true
% 1.49/1.00  --inst_eager_unprocessed_to_passive     true
% 1.49/1.00  --inst_prop_sim_given                   true
% 1.49/1.00  --inst_prop_sim_new                     false
% 1.49/1.00  --inst_subs_new                         false
% 1.49/1.00  --inst_eq_res_simp                      false
% 1.49/1.00  --inst_subs_given                       false
% 1.49/1.00  --inst_orphan_elimination               true
% 1.49/1.00  --inst_learning_loop_flag               true
% 1.49/1.00  --inst_learning_start                   3000
% 1.49/1.00  --inst_learning_factor                  2
% 1.49/1.00  --inst_start_prop_sim_after_learn       3
% 1.49/1.00  --inst_sel_renew                        solver
% 1.49/1.00  --inst_lit_activity_flag                true
% 1.49/1.00  --inst_restr_to_given                   false
% 1.49/1.00  --inst_activity_threshold               500
% 1.49/1.00  --inst_out_proof                        true
% 1.49/1.00  
% 1.49/1.00  ------ Resolution Options
% 1.49/1.00  
% 1.49/1.00  --resolution_flag                       false
% 1.49/1.00  --res_lit_sel                           adaptive
% 1.49/1.00  --res_lit_sel_side                      none
% 1.49/1.00  --res_ordering                          kbo
% 1.49/1.00  --res_to_prop_solver                    active
% 1.49/1.00  --res_prop_simpl_new                    false
% 1.49/1.00  --res_prop_simpl_given                  true
% 1.49/1.00  --res_passive_queue_type                priority_queues
% 1.49/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.49/1.00  --res_passive_queues_freq               [15;5]
% 1.49/1.00  --res_forward_subs                      full
% 1.49/1.00  --res_backward_subs                     full
% 1.49/1.00  --res_forward_subs_resolution           true
% 1.49/1.00  --res_backward_subs_resolution          true
% 1.49/1.00  --res_orphan_elimination                true
% 1.49/1.00  --res_time_limit                        2.
% 1.49/1.00  --res_out_proof                         true
% 1.49/1.00  
% 1.49/1.00  ------ Superposition Options
% 1.49/1.00  
% 1.49/1.00  --superposition_flag                    true
% 1.49/1.00  --sup_passive_queue_type                priority_queues
% 1.49/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.49/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.49/1.00  --demod_completeness_check              fast
% 1.49/1.00  --demod_use_ground                      true
% 1.49/1.00  --sup_to_prop_solver                    passive
% 1.49/1.00  --sup_prop_simpl_new                    true
% 1.49/1.00  --sup_prop_simpl_given                  true
% 1.49/1.00  --sup_fun_splitting                     false
% 1.49/1.00  --sup_smt_interval                      50000
% 1.49/1.00  
% 1.49/1.00  ------ Superposition Simplification Setup
% 1.49/1.00  
% 1.49/1.00  --sup_indices_passive                   []
% 1.49/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.49/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.49/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.00  --sup_full_bw                           [BwDemod]
% 1.49/1.00  --sup_immed_triv                        [TrivRules]
% 1.49/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.49/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.00  --sup_immed_bw_main                     []
% 1.49/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.49/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.49/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.49/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.49/1.00  
% 1.49/1.00  ------ Combination Options
% 1.49/1.00  
% 1.49/1.00  --comb_res_mult                         3
% 1.49/1.00  --comb_sup_mult                         2
% 1.49/1.00  --comb_inst_mult                        10
% 1.49/1.00  
% 1.49/1.00  ------ Debug Options
% 1.49/1.00  
% 1.49/1.00  --dbg_backtrace                         false
% 1.49/1.00  --dbg_dump_prop_clauses                 false
% 1.49/1.00  --dbg_dump_prop_clauses_file            -
% 1.49/1.00  --dbg_out_stat                          false
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  ------ Proving...
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  % SZS status Theorem for theBenchmark.p
% 1.49/1.00  
% 1.49/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.49/1.00  
% 1.49/1.00  fof(f9,conjecture,(
% 1.49/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)))))))))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f10,negated_conjecture,(
% 1.49/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5)))))))))),
% 1.49/1.00    inference(negated_conjecture,[],[f9])).
% 1.49/1.00  
% 1.49/1.00  fof(f23,plain,(
% 1.49/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.49/1.00    inference(ennf_transformation,[],[f10])).
% 1.49/1.00  
% 1.49/1.00  fof(f24,plain,(
% 1.49/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/1.00    inference(flattening,[],[f23])).
% 1.49/1.00  
% 1.49/1.00  fof(f30,plain,(
% 1.49/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) => (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),sK5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) & r2_hidden(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.49/1.00    introduced(choice_axiom,[])).
% 1.49/1.00  
% 1.49/1.00  fof(f29,plain,(
% 1.49/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,sK4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.49/1.00    introduced(choice_axiom,[])).
% 1.49/1.00  
% 1.49/1.00  fof(f28,plain,(
% 1.49/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,sK3,X2,X4),X5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.49/1.00    introduced(choice_axiom,[])).
% 1.49/1.00  
% 1.49/1.00  fof(f27,plain,(
% 1.49/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,sK2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.49/1.00    introduced(choice_axiom,[])).
% 1.49/1.00  
% 1.49/1.00  fof(f26,plain,(
% 1.49/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,sK1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.49/1.00    introduced(choice_axiom,[])).
% 1.49/1.00  
% 1.49/1.00  fof(f25,plain,(
% 1.49/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) != k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.49/1.00    introduced(choice_axiom,[])).
% 1.49/1.00  
% 1.49/1.00  fof(f31,plain,(
% 1.49/1.00    (((((k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) & r2_hidden(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.49/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f30,f29,f28,f27,f26,f25])).
% 1.49/1.00  
% 1.49/1.00  fof(f47,plain,(
% 1.49/1.00    m1_pre_topc(sK2,sK0)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f7,axiom,(
% 1.49/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f20,plain,(
% 1.49/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/1.00    inference(ennf_transformation,[],[f7])).
% 1.49/1.00  
% 1.49/1.00  fof(f21,plain,(
% 1.49/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/1.00    inference(flattening,[],[f20])).
% 1.49/1.00  
% 1.49/1.00  fof(f38,plain,(
% 1.49/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f21])).
% 1.49/1.00  
% 1.49/1.00  fof(f51,plain,(
% 1.49/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f50,plain,(
% 1.49/1.00    v1_funct_1(sK4)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f52,plain,(
% 1.49/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f4,axiom,(
% 1.49/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f15,plain,(
% 1.49/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.49/1.00    inference(ennf_transformation,[],[f4])).
% 1.49/1.00  
% 1.49/1.00  fof(f16,plain,(
% 1.49/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.49/1.00    inference(flattening,[],[f15])).
% 1.49/1.00  
% 1.49/1.00  fof(f35,plain,(
% 1.49/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f16])).
% 1.49/1.00  
% 1.49/1.00  fof(f43,plain,(
% 1.49/1.00    ~v2_struct_0(sK1)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f44,plain,(
% 1.49/1.00    v2_pre_topc(sK1)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f45,plain,(
% 1.49/1.00    l1_pre_topc(sK1)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f1,axiom,(
% 1.49/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f11,plain,(
% 1.49/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.49/1.00    inference(ennf_transformation,[],[f1])).
% 1.49/1.00  
% 1.49/1.00  fof(f32,plain,(
% 1.49/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f11])).
% 1.49/1.00  
% 1.49/1.00  fof(f55,plain,(
% 1.49/1.00    r2_hidden(sK5,u1_struct_0(sK2))),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f5,axiom,(
% 1.49/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f17,plain,(
% 1.49/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.49/1.00    inference(ennf_transformation,[],[f5])).
% 1.49/1.00  
% 1.49/1.00  fof(f18,plain,(
% 1.49/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.49/1.00    inference(flattening,[],[f17])).
% 1.49/1.00  
% 1.49/1.00  fof(f36,plain,(
% 1.49/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f18])).
% 1.49/1.00  
% 1.49/1.00  fof(f8,axiom,(
% 1.49/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f22,plain,(
% 1.49/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.49/1.00    inference(ennf_transformation,[],[f8])).
% 1.49/1.00  
% 1.49/1.00  fof(f39,plain,(
% 1.49/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f22])).
% 1.49/1.00  
% 1.49/1.00  fof(f6,axiom,(
% 1.49/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f19,plain,(
% 1.49/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.49/1.00    inference(ennf_transformation,[],[f6])).
% 1.49/1.00  
% 1.49/1.00  fof(f37,plain,(
% 1.49/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f19])).
% 1.49/1.00  
% 1.49/1.00  fof(f3,axiom,(
% 1.49/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f14,plain,(
% 1.49/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/1.00    inference(ennf_transformation,[],[f3])).
% 1.49/1.00  
% 1.49/1.00  fof(f34,plain,(
% 1.49/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/1.00    inference(cnf_transformation,[],[f14])).
% 1.49/1.00  
% 1.49/1.00  fof(f2,axiom,(
% 1.49/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 1.49/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.49/1.00  
% 1.49/1.00  fof(f12,plain,(
% 1.49/1.00    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/1.00    inference(ennf_transformation,[],[f2])).
% 1.49/1.00  
% 1.49/1.00  fof(f13,plain,(
% 1.49/1.00    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/1.00    inference(flattening,[],[f12])).
% 1.49/1.00  
% 1.49/1.00  fof(f33,plain,(
% 1.49/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.49/1.00    inference(cnf_transformation,[],[f13])).
% 1.49/1.00  
% 1.49/1.00  fof(f56,plain,(
% 1.49/1.00    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f54,plain,(
% 1.49/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f53,plain,(
% 1.49/1.00    m1_pre_topc(sK2,sK3)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f49,plain,(
% 1.49/1.00    m1_pre_topc(sK3,sK0)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f42,plain,(
% 1.49/1.00    l1_pre_topc(sK0)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f41,plain,(
% 1.49/1.00    v2_pre_topc(sK0)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  fof(f40,plain,(
% 1.49/1.00    ~v2_struct_0(sK0)),
% 1.49/1.00    inference(cnf_transformation,[],[f31])).
% 1.49/1.00  
% 1.49/1.00  cnf(c_17,negated_conjecture,
% 1.49/1.00      ( m1_pre_topc(sK2,sK0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_617,negated_conjecture,
% 1.49/1.00      ( m1_pre_topc(sK2,sK0) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_948,plain,
% 1.49/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_6,plain,
% 1.49/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.49/1.00      | ~ m1_pre_topc(X3,X1)
% 1.49/1.00      | ~ m1_pre_topc(X3,X4)
% 1.49/1.00      | ~ m1_pre_topc(X1,X4)
% 1.49/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.49/1.00      | v2_struct_0(X4)
% 1.49/1.00      | v2_struct_0(X2)
% 1.49/1.00      | ~ v2_pre_topc(X2)
% 1.49/1.00      | ~ v2_pre_topc(X4)
% 1.49/1.00      | ~ l1_pre_topc(X4)
% 1.49/1.00      | ~ l1_pre_topc(X2)
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_13,negated_conjecture,
% 1.49/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 1.49/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_375,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.49/1.00      | ~ m1_pre_topc(X0,X2)
% 1.49/1.00      | ~ m1_pre_topc(X1,X2)
% 1.49/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 1.49/1.00      | v2_struct_0(X4)
% 1.49/1.00      | v2_struct_0(X2)
% 1.49/1.00      | ~ v2_pre_topc(X4)
% 1.49/1.00      | ~ v2_pre_topc(X2)
% 1.49/1.00      | ~ l1_pre_topc(X4)
% 1.49/1.00      | ~ l1_pre_topc(X2)
% 1.49/1.00      | ~ v1_funct_1(X3)
% 1.49/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 1.49/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.49/1.00      | u1_struct_0(X4) != u1_struct_0(sK1)
% 1.49/1.00      | sK4 != X3 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_376,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.49/1.00      | ~ m1_pre_topc(X2,X0)
% 1.49/1.00      | ~ m1_pre_topc(X2,X1)
% 1.49/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 1.49/1.00      | v2_struct_0(X1)
% 1.49/1.00      | v2_struct_0(X3)
% 1.49/1.00      | ~ v2_pre_topc(X1)
% 1.49/1.00      | ~ v2_pre_topc(X3)
% 1.49/1.00      | ~ l1_pre_topc(X1)
% 1.49/1.00      | ~ l1_pre_topc(X3)
% 1.49/1.00      | ~ v1_funct_1(sK4)
% 1.49/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 1.49/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.49/1.00      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_14,negated_conjecture,
% 1.49/1.00      ( v1_funct_1(sK4) ),
% 1.49/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_380,plain,
% 1.49/1.00      ( ~ l1_pre_topc(X3)
% 1.49/1.00      | ~ l1_pre_topc(X1)
% 1.49/1.00      | ~ v2_pre_topc(X3)
% 1.49/1.00      | ~ v2_pre_topc(X1)
% 1.49/1.00      | v2_struct_0(X3)
% 1.49/1.00      | v2_struct_0(X1)
% 1.49/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 1.49/1.00      | ~ m1_pre_topc(X2,X1)
% 1.49/1.00      | ~ m1_pre_topc(X2,X0)
% 1.49/1.00      | ~ m1_pre_topc(X0,X1)
% 1.49/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 1.49/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.49/1.00      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 1.49/1.00      inference(global_propositional_subsumption,
% 1.49/1.00                [status(thm)],
% 1.49/1.00                [c_376,c_14]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_381,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.49/1.00      | ~ m1_pre_topc(X2,X0)
% 1.49/1.00      | ~ m1_pre_topc(X2,X1)
% 1.49/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 1.49/1.00      | v2_struct_0(X1)
% 1.49/1.00      | v2_struct_0(X3)
% 1.49/1.00      | ~ v2_pre_topc(X1)
% 1.49/1.00      | ~ v2_pre_topc(X3)
% 1.49/1.00      | ~ l1_pre_topc(X1)
% 1.49/1.00      | ~ l1_pre_topc(X3)
% 1.49/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK4,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK4)
% 1.49/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 1.49/1.00      | u1_struct_0(X3) != u1_struct_0(sK1) ),
% 1.49/1.00      inference(renaming,[status(thm)],[c_380]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_608,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0_54,X1_54)
% 1.49/1.00      | ~ m1_pre_topc(X2_54,X0_54)
% 1.49/1.00      | ~ m1_pre_topc(X2_54,X1_54)
% 1.49/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X3_54))))
% 1.49/1.00      | v2_struct_0(X1_54)
% 1.49/1.00      | v2_struct_0(X3_54)
% 1.49/1.00      | ~ v2_pre_topc(X1_54)
% 1.49/1.00      | ~ v2_pre_topc(X3_54)
% 1.49/1.00      | ~ l1_pre_topc(X1_54)
% 1.49/1.00      | ~ l1_pre_topc(X3_54)
% 1.49/1.00      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X3_54),sK4,u1_struct_0(X2_54)) = k3_tmap_1(X1_54,X3_54,X0_54,X2_54,sK4)
% 1.49/1.00      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 1.49/1.00      | u1_struct_0(X3_54) != u1_struct_0(sK1) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_381]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_957,plain,
% 1.49/1.00      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),sK4,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,sK4)
% 1.49/1.00      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 1.49/1.00      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 1.49/1.00      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 1.49/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 1.49/1.00      | v2_struct_0(X3_54) = iProver_top
% 1.49/1.00      | v2_struct_0(X1_54) = iProver_top
% 1.49/1.00      | v2_pre_topc(X3_54) != iProver_top
% 1.49/1.00      | v2_pre_topc(X1_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(X3_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(X1_54) != iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1620,plain,
% 1.49/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_54),sK4,u1_struct_0(X1_54)) = k3_tmap_1(X2_54,X0_54,sK3,X1_54,sK4)
% 1.49/1.00      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 1.49/1.00      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X1_54,sK3) != iProver_top
% 1.49/1.00      | m1_pre_topc(sK3,X2_54) != iProver_top
% 1.49/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 1.49/1.00      | v2_struct_0(X2_54) = iProver_top
% 1.49/1.00      | v2_struct_0(X0_54) = iProver_top
% 1.49/1.00      | v2_pre_topc(X2_54) != iProver_top
% 1.49/1.00      | v2_pre_topc(X0_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(X0_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(X2_54) != iProver_top ),
% 1.49/1.00      inference(equality_resolution,[status(thm)],[c_957]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1637,plain,
% 1.49/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4)
% 1.49/1.00      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X0_54,sK3) != iProver_top
% 1.49/1.00      | m1_pre_topc(sK3,X1_54) != iProver_top
% 1.49/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.49/1.00      | v2_struct_0(X1_54) = iProver_top
% 1.49/1.00      | v2_struct_0(sK1) = iProver_top
% 1.49/1.00      | v2_pre_topc(X1_54) != iProver_top
% 1.49/1.00      | v2_pre_topc(sK1) != iProver_top
% 1.49/1.00      | l1_pre_topc(X1_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.49/1.00      inference(equality_resolution,[status(thm)],[c_1620]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_12,negated_conjecture,
% 1.49/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.49/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_620,negated_conjecture,
% 1.49/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_945,plain,
% 1.49/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_3,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.49/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_441,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 1.49/1.00      | sK4 != X0 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_442,plain,
% 1.49/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.49/1.00      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_607,plain,
% 1.49/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.49/1.00      | k2_partfun1(X0_52,X1_52,sK4,X2_52) = k7_relat_1(sK4,X2_52) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_442]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_958,plain,
% 1.49/1.00      ( k2_partfun1(X0_52,X1_52,sK4,X2_52) = k7_relat_1(sK4,X2_52)
% 1.49/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1417,plain,
% 1.49/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_52) = k7_relat_1(sK4,X0_52) ),
% 1.49/1.00      inference(superposition,[status(thm)],[c_945,c_958]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1638,plain,
% 1.49/1.00      ( k3_tmap_1(X0_54,sK1,sK3,X1_54,sK4) = k7_relat_1(sK4,u1_struct_0(X1_54))
% 1.49/1.00      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X1_54,sK3) != iProver_top
% 1.49/1.00      | m1_pre_topc(sK3,X0_54) != iProver_top
% 1.49/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.49/1.00      | v2_struct_0(X0_54) = iProver_top
% 1.49/1.00      | v2_struct_0(sK1) = iProver_top
% 1.49/1.00      | v2_pre_topc(X0_54) != iProver_top
% 1.49/1.00      | v2_pre_topc(sK1) != iProver_top
% 1.49/1.00      | l1_pre_topc(X0_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.49/1.00      inference(demodulation,[status(thm)],[c_1637,c_1417]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_21,negated_conjecture,
% 1.49/1.00      ( ~ v2_struct_0(sK1) ),
% 1.49/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_28,plain,
% 1.49/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_20,negated_conjecture,
% 1.49/1.00      ( v2_pre_topc(sK1) ),
% 1.49/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_29,plain,
% 1.49/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_19,negated_conjecture,
% 1.49/1.00      ( l1_pre_topc(sK1) ),
% 1.49/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_30,plain,
% 1.49/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_37,plain,
% 1.49/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1696,plain,
% 1.49/1.00      ( l1_pre_topc(X0_54) != iProver_top
% 1.49/1.00      | v2_struct_0(X0_54) = iProver_top
% 1.49/1.00      | k3_tmap_1(X0_54,sK1,sK3,X1_54,sK4) = k7_relat_1(sK4,u1_struct_0(X1_54))
% 1.49/1.00      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X1_54,sK3) != iProver_top
% 1.49/1.00      | m1_pre_topc(sK3,X0_54) != iProver_top
% 1.49/1.00      | v2_pre_topc(X0_54) != iProver_top ),
% 1.49/1.00      inference(global_propositional_subsumption,
% 1.49/1.00                [status(thm)],
% 1.49/1.00                [c_1638,c_28,c_29,c_30,c_37]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1697,plain,
% 1.49/1.00      ( k3_tmap_1(X0_54,sK1,sK3,X1_54,sK4) = k7_relat_1(sK4,u1_struct_0(X1_54))
% 1.49/1.00      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 1.49/1.00      | m1_pre_topc(X1_54,sK3) != iProver_top
% 1.49/1.00      | m1_pre_topc(sK3,X0_54) != iProver_top
% 1.49/1.00      | v2_struct_0(X0_54) = iProver_top
% 1.49/1.00      | v2_pre_topc(X0_54) != iProver_top
% 1.49/1.00      | l1_pre_topc(X0_54) != iProver_top ),
% 1.49/1.00      inference(renaming,[status(thm)],[c_1696]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1711,plain,
% 1.49/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 1.49/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.49/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.49/1.00      | v2_struct_0(sK0) = iProver_top
% 1.49/1.00      | v2_pre_topc(sK0) != iProver_top
% 1.49/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 1.49/1.00      inference(superposition,[status(thm)],[c_948,c_1697]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_633,plain,
% 1.49/1.00      ( k1_funct_1(X0_52,X1_52) = k1_funct_1(X2_52,X3_52)
% 1.49/1.00      | X0_52 != X2_52
% 1.49/1.00      | X1_52 != X3_52 ),
% 1.49/1.00      theory(equality) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1567,plain,
% 1.49/1.00      ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
% 1.49/1.00      | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k7_relat_1(sK4,u1_struct_0(sK2))
% 1.49/1.00      | sK5 != sK5 ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_633]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_630,plain,
% 1.49/1.00      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 1.49/1.00      theory(equality) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1124,plain,
% 1.49/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_53
% 1.49/1.00      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_53
% 1.49/1.00      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_630]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1485,plain,
% 1.49/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
% 1.49/1.00      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.49/1.00      | k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_1124]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1146,plain,
% 1.49/1.00      ( X0_53 != X1_53
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X1_53
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53 ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_630]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1276,plain,
% 1.49/1.00      ( X0_53 != k1_funct_1(sK4,sK5)
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_1146]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1343,plain,
% 1.49/1.00      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(sK4,sK5)
% 1.49/1.00      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_1276]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_0,plain,
% 1.49/1.00      ( ~ r2_hidden(X0,X1)
% 1.49/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.49/1.00      | ~ v1_xboole_0(X2) ),
% 1.49/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_9,negated_conjecture,
% 1.49/1.00      ( r2_hidden(sK5,u1_struct_0(sK2)) ),
% 1.49/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_287,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.49/1.00      | ~ v1_xboole_0(X1)
% 1.49/1.00      | u1_struct_0(sK2) != X0
% 1.49/1.00      | sK5 != X2 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_288,plain,
% 1.49/1.00      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
% 1.49/1.00      | ~ v1_xboole_0(X0) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_287]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_4,plain,
% 1.49/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.49/1.00      | ~ m1_subset_1(X3,X1)
% 1.49/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | v1_xboole_0(X1)
% 1.49/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.49/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_323,plain,
% 1.49/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.49/1.00      | ~ m1_subset_1(X3,X1)
% 1.49/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X4))
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | X1 != X4
% 1.49/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_288,c_4]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_324,plain,
% 1.49/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.49/1.00      | ~ m1_subset_1(X3,X1)
% 1.49/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X1))
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_354,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,X1)
% 1.49/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.49/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X1))
% 1.49/1.00      | ~ v1_funct_1(X2)
% 1.49/1.00      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 1.49/1.00      | u1_struct_0(sK3) != X1
% 1.49/1.00      | u1_struct_0(sK1) != X3
% 1.49/1.00      | sK4 != X2 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_324,c_13]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_355,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.49/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.49/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 1.49/1.00      | ~ v1_funct_1(sK4)
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_354]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_359,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.49/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ),
% 1.49/1.00      inference(global_propositional_subsumption,
% 1.49/1.00                [status(thm)],
% 1.49/1.00                [c_355,c_14,c_12]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_609,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 1.49/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_52) = k1_funct_1(sK4,X0_52) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_359]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1206,plain,
% 1.49/1.00      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.49/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.49/1.00      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_609]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_7,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.49/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.49/1.00      | ~ l1_pre_topc(X1) ),
% 1.49/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_624,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0_54,X1_54)
% 1.49/1.00      | m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
% 1.49/1.00      | ~ l1_pre_topc(X1_54) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1196,plain,
% 1.49/1.00      ( ~ m1_pre_topc(sK2,sK3)
% 1.49/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.49/1.00      | ~ l1_pre_topc(sK3) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_627,plain,( X0_52 = X0_52 ),theory(equality) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1156,plain,
% 1.49/1.00      ( sK5 = sK5 ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_627]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_5,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_625,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0_54,X1_54)
% 1.49/1.00      | ~ l1_pre_topc(X1_54)
% 1.49/1.00      | l1_pre_topc(X0_54) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1109,plain,
% 1.49/1.00      ( ~ m1_pre_topc(X0_54,sK0)
% 1.49/1.00      | l1_pre_topc(X0_54)
% 1.49/1.00      | ~ l1_pre_topc(sK0) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_625]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1111,plain,
% 1.49/1.00      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_1109]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_2,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | v1_relat_1(X0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1,plain,
% 1.49/1.00      ( ~ r2_hidden(X0,X1)
% 1.49/1.00      | ~ v1_relat_1(X2)
% 1.49/1.00      | ~ v1_funct_1(X2)
% 1.49/1.00      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_272,plain,
% 1.49/1.00      ( ~ v1_relat_1(X0)
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
% 1.49/1.00      | u1_struct_0(sK2) != X1
% 1.49/1.00      | sK5 != X2 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_273,plain,
% 1.49/1.00      ( ~ v1_relat_1(X0)
% 1.49/1.00      | ~ v1_funct_1(X0)
% 1.49/1.00      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_272]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_431,plain,
% 1.49/1.00      ( ~ v1_relat_1(X0)
% 1.49/1.00      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5)
% 1.49/1.00      | sK4 != X0 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_273,c_14]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_432,plain,
% 1.49/1.00      ( ~ v1_relat_1(sK4)
% 1.49/1.00      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_431]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_459,plain,
% 1.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.49/1.00      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)
% 1.49/1.00      | sK4 != X0 ),
% 1.49/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_432]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_460,plain,
% 1.49/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.49/1.00      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_606,plain,
% 1.49/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.49/1.00      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_460]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_1097,plain,
% 1.49/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 1.49/1.00      | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
% 1.49/1.00      inference(instantiation,[status(thm)],[c_606]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_8,negated_conjecture,
% 1.49/1.00      ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.49/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_623,negated_conjecture,
% 1.49/1.00      ( k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.49/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_10,negated_conjecture,
% 1.49/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.49/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_11,negated_conjecture,
% 1.49/1.00      ( m1_pre_topc(sK2,sK3) ),
% 1.49/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_38,plain,
% 1.49/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_15,negated_conjecture,
% 1.49/1.00      ( m1_pre_topc(sK3,sK0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_34,plain,
% 1.49/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_22,negated_conjecture,
% 1.49/1.00      ( l1_pre_topc(sK0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_27,plain,
% 1.49/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_23,negated_conjecture,
% 1.49/1.00      ( v2_pre_topc(sK0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_26,plain,
% 1.49/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_24,negated_conjecture,
% 1.49/1.00      ( ~ v2_struct_0(sK0) ),
% 1.49/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(c_25,plain,
% 1.49/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 1.49/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.49/1.00  
% 1.49/1.00  cnf(contradiction,plain,
% 1.49/1.00      ( $false ),
% 1.49/1.00      inference(minisat,
% 1.49/1.00                [status(thm)],
% 1.49/1.00                [c_1711,c_1567,c_1485,c_1343,c_1206,c_1196,c_1156,c_1111,
% 1.49/1.00                 c_1097,c_623,c_10,c_38,c_11,c_12,c_34,c_15,c_27,c_22,
% 1.49/1.00                 c_26,c_25]) ).
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.49/1.00  
% 1.49/1.00  ------                               Statistics
% 1.49/1.00  
% 1.49/1.00  ------ General
% 1.49/1.00  
% 1.49/1.00  abstr_ref_over_cycles:                  0
% 1.49/1.00  abstr_ref_under_cycles:                 0
% 1.49/1.00  gc_basic_clause_elim:                   0
% 1.49/1.00  forced_gc_time:                         0
% 1.49/1.00  parsing_time:                           0.009
% 1.49/1.00  unif_index_cands_time:                  0.
% 1.49/1.00  unif_index_add_time:                    0.
% 1.49/1.00  orderings_time:                         0.
% 1.49/1.00  out_proof_time:                         0.015
% 1.49/1.00  total_time:                             0.096
% 1.49/1.00  num_of_symbols:                         58
% 1.49/1.00  num_of_terms:                           1868
% 1.49/1.00  
% 1.49/1.00  ------ Preprocessing
% 1.49/1.00  
% 1.49/1.00  num_of_splits:                          0
% 1.49/1.00  num_of_split_atoms:                     0
% 1.49/1.00  num_of_reused_defs:                     0
% 1.49/1.00  num_eq_ax_congr_red:                    15
% 1.49/1.00  num_of_sem_filtered_clauses:            1
% 1.49/1.00  num_of_subtypes:                        3
% 1.49/1.00  monotx_restored_types:                  0
% 1.49/1.00  sat_num_of_epr_types:                   0
% 1.49/1.00  sat_num_of_non_cyclic_types:            0
% 1.49/1.00  sat_guarded_non_collapsed_types:        0
% 1.49/1.00  num_pure_diseq_elim:                    0
% 1.49/1.00  simp_replaced_by:                       0
% 1.49/1.00  res_preprocessed:                       110
% 1.49/1.00  prep_upred:                             0
% 1.49/1.00  prep_unflattend:                        13
% 1.49/1.00  smt_new_axioms:                         0
% 1.49/1.00  pred_elim_cands:                        5
% 1.49/1.00  pred_elim:                              5
% 1.49/1.00  pred_elim_cl:                           5
% 1.49/1.00  pred_elim_cycles:                       9
% 1.49/1.00  merged_defs:                            0
% 1.49/1.00  merged_defs_ncl:                        0
% 1.49/1.00  bin_hyper_res:                          0
% 1.49/1.00  prep_cycles:                            4
% 1.49/1.00  pred_elim_time:                         0.006
% 1.49/1.00  splitting_time:                         0.
% 1.49/1.00  sem_filter_time:                        0.
% 1.49/1.00  monotx_time:                            0.
% 1.49/1.00  subtype_inf_time:                       0.
% 1.49/1.00  
% 1.49/1.00  ------ Problem properties
% 1.49/1.00  
% 1.49/1.00  clauses:                                20
% 1.49/1.00  conjectures:                            14
% 1.49/1.00  epr:                                    12
% 1.49/1.00  horn:                                   19
% 1.49/1.00  ground:                                 14
% 1.49/1.00  unary:                                  14
% 1.49/1.00  binary:                                 2
% 1.49/1.00  lits:                                   40
% 1.49/1.00  lits_eq:                                7
% 1.49/1.00  fd_pure:                                0
% 1.49/1.00  fd_pseudo:                              0
% 1.49/1.00  fd_cond:                                0
% 1.49/1.00  fd_pseudo_cond:                         0
% 1.49/1.00  ac_symbols:                             0
% 1.49/1.00  
% 1.49/1.00  ------ Propositional Solver
% 1.49/1.00  
% 1.49/1.00  prop_solver_calls:                      28
% 1.49/1.00  prop_fast_solver_calls:                 631
% 1.49/1.00  smt_solver_calls:                       0
% 1.49/1.00  smt_fast_solver_calls:                  0
% 1.49/1.00  prop_num_of_clauses:                    449
% 1.49/1.00  prop_preprocess_simplified:             2486
% 1.49/1.00  prop_fo_subsumed:                       11
% 1.49/1.00  prop_solver_time:                       0.
% 1.49/1.00  smt_solver_time:                        0.
% 1.49/1.00  smt_fast_solver_time:                   0.
% 1.49/1.00  prop_fast_solver_time:                  0.
% 1.49/1.00  prop_unsat_core_time:                   0.
% 1.49/1.00  
% 1.49/1.00  ------ QBF
% 1.49/1.00  
% 1.49/1.00  qbf_q_res:                              0
% 1.49/1.00  qbf_num_tautologies:                    0
% 1.49/1.00  qbf_prep_cycles:                        0
% 1.49/1.00  
% 1.49/1.00  ------ BMC1
% 1.49/1.00  
% 1.49/1.00  bmc1_current_bound:                     -1
% 1.49/1.00  bmc1_last_solved_bound:                 -1
% 1.49/1.00  bmc1_unsat_core_size:                   -1
% 1.49/1.00  bmc1_unsat_core_parents_size:           -1
% 1.49/1.00  bmc1_merge_next_fun:                    0
% 1.49/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.49/1.00  
% 1.49/1.00  ------ Instantiation
% 1.49/1.00  
% 1.49/1.00  inst_num_of_clauses:                    162
% 1.49/1.00  inst_num_in_passive:                    5
% 1.49/1.00  inst_num_in_active:                     129
% 1.49/1.00  inst_num_in_unprocessed:                28
% 1.49/1.00  inst_num_of_loops:                      140
% 1.49/1.00  inst_num_of_learning_restarts:          0
% 1.49/1.00  inst_num_moves_active_passive:          6
% 1.49/1.00  inst_lit_activity:                      0
% 1.49/1.00  inst_lit_activity_moves:                0
% 1.49/1.00  inst_num_tautologies:                   0
% 1.49/1.00  inst_num_prop_implied:                  0
% 1.49/1.00  inst_num_existing_simplified:           0
% 1.49/1.00  inst_num_eq_res_simplified:             0
% 1.49/1.00  inst_num_child_elim:                    0
% 1.49/1.00  inst_num_of_dismatching_blockings:      17
% 1.49/1.00  inst_num_of_non_proper_insts:           151
% 1.49/1.00  inst_num_of_duplicates:                 0
% 1.49/1.00  inst_inst_num_from_inst_to_res:         0
% 1.49/1.00  inst_dismatching_checking_time:         0.
% 1.49/1.00  
% 1.49/1.00  ------ Resolution
% 1.49/1.00  
% 1.49/1.00  res_num_of_clauses:                     0
% 1.49/1.00  res_num_in_passive:                     0
% 1.49/1.00  res_num_in_active:                      0
% 1.49/1.00  res_num_of_loops:                       114
% 1.49/1.00  res_forward_subset_subsumed:            39
% 1.49/1.00  res_backward_subset_subsumed:           2
% 1.49/1.00  res_forward_subsumed:                   0
% 1.49/1.00  res_backward_subsumed:                  0
% 1.49/1.00  res_forward_subsumption_resolution:     0
% 1.49/1.00  res_backward_subsumption_resolution:    0
% 1.49/1.00  res_clause_to_clause_subsumption:       51
% 1.49/1.00  res_orphan_elimination:                 0
% 1.49/1.00  res_tautology_del:                      40
% 1.49/1.00  res_num_eq_res_simplified:              0
% 1.49/1.00  res_num_sel_changes:                    0
% 1.49/1.00  res_moves_from_active_to_pass:          0
% 1.49/1.00  
% 1.49/1.00  ------ Superposition
% 1.49/1.00  
% 1.49/1.00  sup_time_total:                         0.
% 1.49/1.00  sup_time_generating:                    0.
% 1.49/1.00  sup_time_sim_full:                      0.
% 1.49/1.00  sup_time_sim_immed:                     0.
% 1.49/1.00  
% 1.49/1.00  sup_num_of_clauses:                     29
% 1.49/1.00  sup_num_in_active:                      26
% 1.49/1.00  sup_num_in_passive:                     3
% 1.49/1.00  sup_num_of_loops:                       26
% 1.49/1.00  sup_fw_superposition:                   7
% 1.49/1.00  sup_bw_superposition:                   1
% 1.49/1.00  sup_immediate_simplified:               1
% 1.49/1.00  sup_given_eliminated:                   0
% 1.49/1.00  comparisons_done:                       0
% 1.49/1.00  comparisons_avoided:                    0
% 1.49/1.00  
% 1.49/1.00  ------ Simplifications
% 1.49/1.00  
% 1.49/1.00  
% 1.49/1.00  sim_fw_subset_subsumed:                 0
% 1.49/1.00  sim_bw_subset_subsumed:                 1
% 1.49/1.00  sim_fw_subsumed:                        0
% 1.49/1.00  sim_bw_subsumed:                        0
% 1.49/1.00  sim_fw_subsumption_res:                 0
% 1.49/1.00  sim_bw_subsumption_res:                 0
% 1.49/1.00  sim_tautology_del:                      0
% 1.49/1.00  sim_eq_tautology_del:                   0
% 1.49/1.00  sim_eq_res_simp:                        0
% 1.49/1.00  sim_fw_demodulated:                     1
% 1.49/1.00  sim_bw_demodulated:                     1
% 1.49/1.00  sim_light_normalised:                   0
% 1.49/1.00  sim_joinable_taut:                      0
% 1.49/1.00  sim_joinable_simp:                      0
% 1.49/1.00  sim_ac_normalised:                      0
% 1.49/1.00  sim_smt_subsumption:                    0
% 1.49/1.00  
%------------------------------------------------------------------------------
