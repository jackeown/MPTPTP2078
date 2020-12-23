%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:33 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  201 (1336 expanded)
%              Number of clauses        :  106 ( 281 expanded)
%              Number of leaves         :   25 ( 595 expanded)
%              Depth                    :   19
%              Number of atoms          : 1004 (18408 expanded)
%              Number of equality atoms :  199 (2672 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,conjecture,(
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
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK5)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK4,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK3,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                            ( ~ r1_tmap_1(X3,sK1,X4,X5)
                            & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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

fof(f58,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f57,f56,f55,f54,f53,f52,f51])).

fof(f90,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
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

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f41])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f80])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_10976,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_515,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1589,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | X0 != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_6309,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_10798,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6309])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1162,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1182,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2413,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1182])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_43,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1863,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

cnf(c_1864,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1863])).

cnf(c_2608,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2413,c_43,c_1864])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1183,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2613,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_1183])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1184,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2724,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2613,c_1184])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1160,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1174,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1172,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1346,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1174,c_1172])).

cnf(c_7051,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1346])).

cnf(c_2414,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1182])).

cnf(c_1865,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

cnf(c_1866,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_2616,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2414,c_43,c_1866])).

cnf(c_2621,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2616,c_1183])).

cnf(c_2727,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2621,c_1184])).

cnf(c_7132,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7051,c_2727])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1175,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5797,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1175])).

cnf(c_7882,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7132,c_43,c_1866,c_5797])).

cnf(c_7891,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_7882])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1176,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1180,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4259,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1180])).

cnf(c_4343,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_4259])).

cnf(c_8417,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7891,c_43,c_1866,c_4343])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1187,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8422,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8417,c_1187])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_41,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_47,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_48,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1177,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4625,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1177])).

cnf(c_4631,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4625,c_27])).

cnf(c_4898,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4631,c_41,c_42,c_43,c_47])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1178,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5523,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4898,c_1178])).

cnf(c_7050,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1346])).

cnf(c_7141,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7050,c_2724])).

cnf(c_3659,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_1175])).

cnf(c_7922,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7141,c_43,c_1864,c_3659])).

cnf(c_7930,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_7922])).

cnf(c_8729,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8422,c_41,c_42,c_43,c_47,c_48,c_5523,c_7930])).

cnf(c_8738,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_8729,c_2727])).

cnf(c_10,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_12,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_293,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_12])).

cnf(c_6686,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_5622,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5523])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2342,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2372,plain,
    ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(X0,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_3086,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,X0)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_4552,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3086])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2739,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_31])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1167,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1216,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1167,c_24])).

cnf(c_1479,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1216])).

cnf(c_23,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1168,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1239,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1168,c_24])).

cnf(c_1445,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1239])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10976,c_10798,c_8738,c_6686,c_5622,c_4552,c_2739,c_1863,c_1479,c_1445,c_22,c_26,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.66/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/0.98  
% 3.66/0.98  ------  iProver source info
% 3.66/0.98  
% 3.66/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.66/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/0.98  git: non_committed_changes: false
% 3.66/0.98  git: last_make_outside_of_git: false
% 3.66/0.98  
% 3.66/0.98  ------ 
% 3.66/0.98  ------ Parsing...
% 3.66/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/0.98  ------ Proving...
% 3.66/0.98  ------ Problem Properties 
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  clauses                                 39
% 3.66/0.98  conjectures                             19
% 3.66/0.98  EPR                                     20
% 3.66/0.98  Horn                                    35
% 3.66/0.98  unary                                   20
% 3.66/0.98  binary                                  3
% 3.66/0.98  lits                                    127
% 3.66/0.98  lits eq                                 5
% 3.66/0.98  fd_pure                                 0
% 3.66/0.98  fd_pseudo                               0
% 3.66/0.98  fd_cond                                 0
% 3.66/0.98  fd_pseudo_cond                          1
% 3.66/0.98  AC symbols                              0
% 3.66/0.98  
% 3.66/0.98  ------ Input Options Time Limit: Unbounded
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  ------ 
% 3.66/0.98  Current options:
% 3.66/0.98  ------ 
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  ------ Proving...
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  % SZS status Theorem for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  fof(f6,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f25,plain,(
% 3.66/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f6])).
% 3.66/0.98  
% 3.66/0.98  fof(f26,plain,(
% 3.66/0.98    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(flattening,[],[f25])).
% 3.66/0.98  
% 3.66/0.98  fof(f66,plain,(
% 3.66/0.98    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f26])).
% 3.66/0.98  
% 3.66/0.98  fof(f17,conjecture,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f18,negated_conjecture,(
% 3.66/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.66/0.98    inference(negated_conjecture,[],[f17])).
% 3.66/0.98  
% 3.66/0.98  fof(f43,plain,(
% 3.66/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f18])).
% 3.66/0.98  
% 3.66/0.98  fof(f44,plain,(
% 3.66/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f43])).
% 3.66/0.98  
% 3.66/0.98  fof(f57,plain,(
% 3.66/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f56,plain,(
% 3.66/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f55,plain,(
% 3.66/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f54,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f53,plain,(
% 3.66/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f52,plain,(
% 3.66/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f51,plain,(
% 3.66/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f58,plain,(
% 3.66/0.98    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f57,f56,f55,f54,f53,f52,f51])).
% 3.66/0.98  
% 3.66/0.98  fof(f90,plain,(
% 3.66/0.98    m1_pre_topc(sK3,sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f5,axiom,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f24,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f5])).
% 3.66/0.98  
% 3.66/0.98  fof(f65,plain,(
% 3.66/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f24])).
% 3.66/0.98  
% 3.66/0.98  fof(f83,plain,(
% 3.66/0.98    l1_pre_topc(sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f4,axiom,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f23,plain,(
% 3.66/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f4])).
% 3.66/0.98  
% 3.66/0.98  fof(f64,plain,(
% 3.66/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f23])).
% 3.66/0.98  
% 3.66/0.98  fof(f3,axiom,(
% 3.66/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f22,plain,(
% 3.66/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f3])).
% 3.66/0.98  
% 3.66/0.98  fof(f63,plain,(
% 3.66/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f22])).
% 3.66/0.98  
% 3.66/0.98  fof(f88,plain,(
% 3.66/0.98    m1_pre_topc(sK2,sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f14,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f37,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f14])).
% 3.66/0.98  
% 3.66/0.98  fof(f38,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(flattening,[],[f37])).
% 3.66/0.98  
% 3.66/0.98  fof(f49,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f38])).
% 3.66/0.98  
% 3.66/0.98  fof(f77,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f49])).
% 3.66/0.98  
% 3.66/0.98  fof(f15,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f39,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f15])).
% 3.66/0.98  
% 3.66/0.98  fof(f40,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(flattening,[],[f39])).
% 3.66/0.98  
% 3.66/0.98  fof(f78,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f40])).
% 3.66/0.98  
% 3.66/0.98  fof(f13,axiom,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f36,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f13])).
% 3.66/0.98  
% 3.66/0.98  fof(f75,plain,(
% 3.66/0.98    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f36])).
% 3.66/0.98  
% 3.66/0.98  fof(f12,axiom,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f35,plain,(
% 3.66/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f12])).
% 3.66/0.98  
% 3.66/0.98  fof(f74,plain,(
% 3.66/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f35])).
% 3.66/0.98  
% 3.66/0.98  fof(f94,plain,(
% 3.66/0.98    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f7,axiom,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f19,plain,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 3.66/0.98    inference(pure_predicate_removal,[],[f7])).
% 3.66/0.98  
% 3.66/0.98  fof(f27,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f19])).
% 3.66/0.98  
% 3.66/0.98  fof(f67,plain,(
% 3.66/0.98    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f27])).
% 3.66/0.98  
% 3.66/0.98  fof(f1,axiom,(
% 3.66/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f45,plain,(
% 3.66/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.66/0.98    inference(nnf_transformation,[],[f1])).
% 3.66/0.98  
% 3.66/0.98  fof(f46,plain,(
% 3.66/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.66/0.98    inference(flattening,[],[f45])).
% 3.66/0.98  
% 3.66/0.98  fof(f61,plain,(
% 3.66/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f46])).
% 3.66/0.98  
% 3.66/0.98  fof(f81,plain,(
% 3.66/0.98    ~v2_struct_0(sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f82,plain,(
% 3.66/0.98    v2_pre_topc(sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f87,plain,(
% 3.66/0.98    ~v2_struct_0(sK2)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f11,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f33,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f11])).
% 3.66/0.98  
% 3.66/0.98  fof(f34,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f33])).
% 3.66/0.98  
% 3.66/0.98  fof(f73,plain,(
% 3.66/0.98    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f10,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f31,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f10])).
% 3.66/0.98  
% 3.66/0.98  fof(f32,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f31])).
% 3.66/0.98  
% 3.66/0.98  fof(f72,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f32])).
% 3.66/0.98  
% 3.66/0.98  fof(f8,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f28,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f8])).
% 3.66/0.98  
% 3.66/0.98  fof(f29,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(flattening,[],[f28])).
% 3.66/0.98  
% 3.66/0.98  fof(f47,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f29])).
% 3.66/0.98  
% 3.66/0.98  fof(f48,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(flattening,[],[f47])).
% 3.66/0.98  
% 3.66/0.98  fof(f69,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f48])).
% 3.66/0.98  
% 3.66/0.98  fof(f103,plain,(
% 3.66/0.98    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.98    inference(equality_resolution,[],[f69])).
% 3.66/0.98  
% 3.66/0.98  fof(f9,axiom,(
% 3.66/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f30,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.66/0.98    inference(ennf_transformation,[],[f9])).
% 3.66/0.98  
% 3.66/0.98  fof(f71,plain,(
% 3.66/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f30])).
% 3.66/0.98  
% 3.66/0.98  fof(f16,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f41,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f16])).
% 3.66/0.98  
% 3.66/0.98  fof(f42,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(flattening,[],[f41])).
% 3.66/0.98  
% 3.66/0.98  fof(f50,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.98    inference(nnf_transformation,[],[f42])).
% 3.66/0.98  
% 3.66/0.98  fof(f80,plain,(
% 3.66/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f50])).
% 3.66/0.98  
% 3.66/0.98  fof(f105,plain,(
% 3.66/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.98    inference(equality_resolution,[],[f80])).
% 3.66/0.98  
% 3.66/0.98  fof(f2,axiom,(
% 3.66/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.66/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f20,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.98    inference(ennf_transformation,[],[f2])).
% 3.66/0.98  
% 3.66/0.98  fof(f21,plain,(
% 3.66/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.98    inference(flattening,[],[f20])).
% 3.66/0.98  
% 3.66/0.98  fof(f62,plain,(
% 3.66/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f21])).
% 3.66/0.98  
% 3.66/0.98  fof(f96,plain,(
% 3.66/0.98    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f97,plain,(
% 3.66/0.98    sK5 = sK6),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f98,plain,(
% 3.66/0.98    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f99,plain,(
% 3.66/0.98    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f95,plain,(
% 3.66/0.98    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f93,plain,(
% 3.66/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f92,plain,(
% 3.66/0.98    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f91,plain,(
% 3.66/0.98    v1_funct_1(sK4)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f89,plain,(
% 3.66/0.98    ~v2_struct_0(sK3)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f86,plain,(
% 3.66/0.98    l1_pre_topc(sK1)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f85,plain,(
% 3.66/0.98    v2_pre_topc(sK1)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  fof(f84,plain,(
% 3.66/0.98    ~v2_struct_0(sK1)),
% 3.66/0.98    inference(cnf_transformation,[],[f58])).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7,plain,
% 3.66/0.98      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.66/0.98      | ~ l1_pre_topc(X0)
% 3.66/0.98      | ~ v2_pre_topc(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_10976,plain,
% 3.66/0.98      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.66/0.98      | ~ l1_pre_topc(sK3)
% 3.66/0.98      | ~ v2_pre_topc(sK3) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_515,plain,
% 3.66/0.98      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 3.66/0.98      theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1589,plain,
% 3.66/0.98      ( v3_pre_topc(X0,X1)
% 3.66/0.98      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.66/0.98      | X0 != k2_struct_0(X1) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_515]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_6309,plain,
% 3.66/0.98      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.66/0.98      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.66/0.98      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_10798,plain,
% 3.66/0.98      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.66/0.98      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.66/0.98      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_6309]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_31,negated_conjecture,
% 3.66/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1162,plain,
% 3.66/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_6,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1182,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top
% 3.66/0.98      | l1_pre_topc(X0) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2413,plain,
% 3.66/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_1162,c_1182]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_38,negated_conjecture,
% 3.66/0.98      ( l1_pre_topc(sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_43,plain,
% 3.66/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1863,plain,
% 3.66/0.98      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_6,c_31]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1864,plain,
% 3.66/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1863]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2608,plain,
% 3.66/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_2413,c_43,c_1864]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_5,plain,
% 3.66/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1183,plain,
% 3.66/0.98      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2613,plain,
% 3.66/0.98      ( l1_struct_0(sK3) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2608,c_1183]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4,plain,
% 3.66/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1184,plain,
% 3.66/0.98      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.66/0.98      | l1_struct_0(X0) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2724,plain,
% 3.66/0.98      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2613,c_1184]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_33,negated_conjecture,
% 3.66/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1160,plain,
% 3.66/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_17,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ m1_pre_topc(X2,X1)
% 3.66/0.98      | ~ m1_pre_topc(X0,X2)
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1174,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(X0,X2) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top
% 3.66/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_19,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ m1_pre_topc(X2,X0)
% 3.66/0.98      | m1_pre_topc(X2,X1)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1172,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.66/0.98      | m1_pre_topc(X2,X1) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top
% 3.66/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1346,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(X2,X0) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top
% 3.66/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(forward_subsumption_resolution,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1174,c_1172]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7051,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_1160,c_1346]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2414,plain,
% 3.66/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | l1_pre_topc(sK2) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_1160,c_1182]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1865,plain,
% 3.66/0.98      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_6,c_33]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1866,plain,
% 3.66/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | l1_pre_topc(sK2) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2616,plain,
% 3.66/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_2414,c_43,c_1866]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2621,plain,
% 3.66/0.98      ( l1_struct_0(sK2) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2616,c_1183]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2727,plain,
% 3.66/0.98      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2621,c_1184]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7132,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_7051,c_2727]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_16,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.66/0.98      | ~ l1_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1175,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_5797,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2727,c_1175]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7882,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_7132,c_43,c_1866,c_5797]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7891,plain,
% 3.66/0.98      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.66/0.98      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2724,c_7882]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_15,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1176,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.66/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_27,negated_conjecture,
% 3.66/0.98      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.66/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.66/0.98      | ~ l1_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1180,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4259,plain,
% 3.66/0.98      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.66/0.98      | m1_pre_topc(sK3,X0) = iProver_top
% 3.66/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_27,c_1180]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4343,plain,
% 3.66/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_1176,c_4259]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8417,plain,
% 3.66/0.98      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_7891,c_43,c_1866,c_4343]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_0,plain,
% 3.66/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.66/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1187,plain,
% 3.66/0.98      ( X0 = X1
% 3.66/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.66/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8422,plain,
% 3.66/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.66/0.98      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_8417,c_1187]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_40,negated_conjecture,
% 3.66/0.98      ( ~ v2_struct_0(sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_41,plain,
% 3.66/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_39,negated_conjecture,
% 3.66/0.98      ( v2_pre_topc(sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_42,plain,
% 3.66/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_34,negated_conjecture,
% 3.66/0.98      ( ~ v2_struct_0(sK2) ),
% 3.66/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_47,plain,
% 3.66/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_48,plain,
% 3.66/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_14,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1)
% 3.66/0.98      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1177,plain,
% 3.66/0.98      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 3.66/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | v2_struct_0(X1) = iProver_top
% 3.66/0.98      | v2_struct_0(X0) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top
% 3.66/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4625,plain,
% 3.66/0.98      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 3.66/0.98      | v2_struct_0(sK0) = iProver_top
% 3.66/0.98      | v2_struct_0(sK2) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_1160,c_1177]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4631,plain,
% 3.66/0.98      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 3.66/0.98      | v2_struct_0(sK0) = iProver_top
% 3.66/0.98      | v2_struct_0(sK2) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_4625,c_27]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4898,plain,
% 3.66/0.98      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_4631,c_41,c_42,c_43,c_47]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_13,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ m1_pre_topc(X2,X1)
% 3.66/0.98      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | v2_struct_0(X2)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1178,plain,
% 3.66/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(X2,X1) != iProver_top
% 3.66/0.98      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 3.66/0.98      | v2_struct_0(X1) = iProver_top
% 3.66/0.98      | v2_struct_0(X0) = iProver_top
% 3.66/0.98      | v2_struct_0(X2) = iProver_top
% 3.66/0.98      | l1_pre_topc(X1) != iProver_top
% 3.66/0.98      | v2_pre_topc(X1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_5523,plain,
% 3.66/0.98      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.66/0.98      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.66/0.98      | v2_struct_0(sK0) = iProver_top
% 3.66/0.98      | v2_struct_0(sK2) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_4898,c_1178]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7050,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_1162,c_1346]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7141,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_7050,c_2724]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3659,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.66/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2724,c_1175]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7922,plain,
% 3.66/0.98      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.66/0.98      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_7141,c_43,c_1864,c_3659]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7930,plain,
% 3.66/0.98      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.66/0.98      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2727,c_7922]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8729,plain,
% 3.66/0.98      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_8422,c_41,c_42,c_43,c_47,c_48,c_5523,c_7930]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8738,plain,
% 3.66/0.98      ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.66/0.98      inference(demodulation,[status(thm)],[c_8729,c_2727]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_10,plain,
% 3.66/0.98      ( v1_tsep_1(X0,X1)
% 3.66/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.66/0.98      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.66/0.98      | ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_12,plain,
% 3.66/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.66/0.98      | ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ l1_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_293,plain,
% 3.66/0.98      ( v1_tsep_1(X0,X1)
% 3.66/0.98      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.66/0.98      | ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_10,c_12]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_6686,plain,
% 3.66/0.98      ( v1_tsep_1(sK2,sK3)
% 3.66/0.98      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.66/0.98      | ~ m1_pre_topc(sK2,sK3)
% 3.66/0.98      | ~ l1_pre_topc(sK3)
% 3.66/0.98      | ~ v2_pre_topc(sK3) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_293]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_5622,plain,
% 3.66/0.98      ( ~ m1_pre_topc(sK2,sK0)
% 3.66/0.98      | m1_pre_topc(sK2,sK3)
% 3.66/0.98      | v2_struct_0(sK0)
% 3.66/0.98      | v2_struct_0(sK2)
% 3.66/0.98      | ~ l1_pre_topc(sK0)
% 3.66/0.98      | ~ v2_pre_topc(sK0) ),
% 3.66/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5523]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_20,plain,
% 3.66/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.66/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.66/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.66/0.98      | ~ v1_tsep_1(X4,X0)
% 3.66/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.66/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.66/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_pre_topc(X4,X5)
% 3.66/0.98      | ~ m1_pre_topc(X4,X0)
% 3.66/0.98      | ~ m1_pre_topc(X0,X5)
% 3.66/0.98      | ~ v1_funct_1(X2)
% 3.66/0.98      | v2_struct_0(X5)
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | v2_struct_0(X4)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | ~ l1_pre_topc(X5)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X5)
% 3.66/0.98      | ~ v2_pre_topc(X1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2342,plain,
% 3.66/0.98      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.66/0.98      | r1_tmap_1(X3,X1,sK4,X4)
% 3.66/0.98      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
% 3.66/0.98      | ~ v1_tsep_1(X0,X3)
% 3.66/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.66/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.66/0.98      | ~ m1_pre_topc(X0,X3)
% 3.66/0.98      | ~ m1_pre_topc(X0,X2)
% 3.66/0.98      | ~ m1_pre_topc(X3,X2)
% 3.66/0.98      | ~ v1_funct_1(sK4)
% 3.66/0.98      | v2_struct_0(X3)
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | v2_struct_0(X2)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ l1_pre_topc(X2)
% 3.66/0.98      | ~ v2_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X2) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2372,plain,
% 3.66/0.98      ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
% 3.66/0.98      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.66/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.66/0.98      | ~ v1_tsep_1(X0,sK3)
% 3.66/0.98      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 3.66/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.66/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.66/0.98      | ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ m1_pre_topc(X0,sK3)
% 3.66/0.98      | ~ m1_pre_topc(sK3,X1)
% 3.66/0.98      | ~ v1_funct_1(sK4)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | v2_struct_0(X1)
% 3.66/0.98      | v2_struct_0(sK1)
% 3.66/0.98      | v2_struct_0(sK3)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ l1_pre_topc(sK1)
% 3.66/0.98      | ~ v2_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(sK1) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2342]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3086,plain,
% 3.66/0.98      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
% 3.66/0.98      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.66/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.66/0.98      | ~ v1_tsep_1(sK2,sK3)
% 3.66/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.66/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.66/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.66/0.98      | ~ m1_pre_topc(sK2,X0)
% 3.66/0.98      | ~ m1_pre_topc(sK2,sK3)
% 3.66/0.98      | ~ m1_pre_topc(sK3,X0)
% 3.66/0.98      | ~ v1_funct_1(sK4)
% 3.66/0.98      | v2_struct_0(X0)
% 3.66/0.98      | v2_struct_0(sK2)
% 3.66/0.98      | v2_struct_0(sK1)
% 3.66/0.98      | v2_struct_0(sK3)
% 3.66/0.98      | ~ l1_pre_topc(X0)
% 3.66/0.98      | ~ l1_pre_topc(sK1)
% 3.66/0.98      | ~ v2_pre_topc(X0)
% 3.66/0.98      | ~ v2_pre_topc(sK1) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_2372]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4552,plain,
% 3.66/0.98      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 3.66/0.98      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.66/0.98      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.66/0.98      | ~ v1_tsep_1(sK2,sK3)
% 3.66/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.66/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.66/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.66/0.98      | ~ m1_pre_topc(sK2,sK0)
% 3.66/0.98      | ~ m1_pre_topc(sK2,sK3)
% 3.66/0.98      | ~ m1_pre_topc(sK3,sK0)
% 3.66/0.98      | ~ v1_funct_1(sK4)
% 3.66/0.98      | v2_struct_0(sK0)
% 3.66/0.98      | v2_struct_0(sK2)
% 3.66/0.98      | v2_struct_0(sK1)
% 3.66/0.98      | v2_struct_0(sK3)
% 3.66/0.98      | ~ l1_pre_topc(sK0)
% 3.66/0.98      | ~ l1_pre_topc(sK1)
% 3.66/0.98      | ~ v2_pre_topc(sK0)
% 3.66/0.98      | ~ v2_pre_topc(sK1) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_3086]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3,plain,
% 3.66/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.98      | ~ l1_pre_topc(X1)
% 3.66/0.98      | ~ v2_pre_topc(X1)
% 3.66/0.98      | v2_pre_topc(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2739,plain,
% 3.66/0.98      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 3.66/0.98      inference(resolution,[status(thm)],[c_3,c_31]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_25,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.66/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1167,plain,
% 3.66/0.98      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_24,negated_conjecture,
% 3.66/0.98      ( sK5 = sK6 ),
% 3.66/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1216,plain,
% 3.66/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_1167,c_24]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1479,plain,
% 3.66/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 3.66/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1216]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_23,negated_conjecture,
% 3.66/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.66/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1168,plain,
% 3.66/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1239,plain,
% 3.66/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_1168,c_24]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1445,plain,
% 3.66/0.98      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 3.66/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1239]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_22,negated_conjecture,
% 3.66/0.98      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.66/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_26,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.66/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_28,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.66/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_29,negated_conjecture,
% 3.66/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.66/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_30,negated_conjecture,
% 3.66/0.98      ( v1_funct_1(sK4) ),
% 3.66/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_32,negated_conjecture,
% 3.66/0.98      ( ~ v2_struct_0(sK3) ),
% 3.66/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_35,negated_conjecture,
% 3.66/0.98      ( l1_pre_topc(sK1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_36,negated_conjecture,
% 3.66/0.98      ( v2_pre_topc(sK1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_37,negated_conjecture,
% 3.66/0.98      ( ~ v2_struct_0(sK1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(contradiction,plain,
% 3.66/0.98      ( $false ),
% 3.66/0.98      inference(minisat,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_10976,c_10798,c_8738,c_6686,c_5622,c_4552,c_2739,
% 3.66/0.98                 c_1863,c_1479,c_1445,c_22,c_26,c_28,c_29,c_30,c_31,c_32,
% 3.66/0.98                 c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  ------                               Statistics
% 3.66/0.98  
% 3.66/0.98  ------ Selected
% 3.66/0.98  
% 3.66/0.98  total_time:                             0.353
% 3.66/0.98  
%------------------------------------------------------------------------------
