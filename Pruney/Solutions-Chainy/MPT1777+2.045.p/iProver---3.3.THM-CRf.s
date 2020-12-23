%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:34 EST 2020

% Result     : Theorem 27.33s
% Output     : CNFRefutation 27.33s
% Verified   : 
% Statistics : Number of formulae       :  208 (1011 expanded)
%              Number of clauses        :  119 ( 237 expanded)
%              Number of leaves         :   26 ( 430 expanded)
%              Depth                    :   19
%              Number of atoms          : 1066 (13091 expanded)
%              Number of equality atoms :  225 (1907 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f49,f48,f47,f46,f45,f44,f43])).

fof(f81,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f83,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f90,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1055,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_18301,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(sK3,X4,sK4,sK6)
    | X1 != X4
    | X3 != sK6
    | X2 != sK4
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_30227,plain,
    ( r1_tmap_1(X0,X1,sK4,X2)
    | ~ r1_tmap_1(sK3,X3,sK4,sK6)
    | X1 != X3
    | X2 != sK6
    | X0 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_18301])).

cnf(c_57337,plain,
    ( r1_tmap_1(X0,X1,sK4,sK5)
    | ~ r1_tmap_1(sK3,X2,sK4,sK6)
    | X1 != X2
    | X0 != sK3
    | sK5 != sK6
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_30227])).

cnf(c_58619,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,sK6)
    | r1_tmap_1(sK3,X1,sK4,sK5)
    | X1 != X0
    | sK5 != sK6
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_57337])).

cnf(c_58621,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | sK5 != sK6
    | sK4 != sK4
    | sK1 != sK1
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_58619])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1798,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1808,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3104,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_1808])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2485,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_8,c_30])).

cnf(c_2486,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2485])).

cnf(c_3768,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3104,c_42,c_2486])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_475,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_1787,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_3772,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3768,c_1787])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1796,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3105,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1808])).

cnf(c_2487,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_32])).

cnf(c_2488,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2487])).

cnf(c_3875,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3105,c_42,c_2488])).

cnf(c_3879,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3875,c_1787])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1806,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10711,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3879,c_1806])).

cnf(c_11348,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10711,c_42,c_2488])).

cnf(c_11349,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11348])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11358,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11349,c_1810])).

cnf(c_11368,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3772,c_11358])).

cnf(c_9228,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3772,c_1806])).

cnf(c_9747,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9228,c_42,c_2486])).

cnf(c_9748,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9747])).

cnf(c_9756,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9748,c_1810])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1813,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9936,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK3)
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9756,c_1813])).

cnf(c_10679,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3879,c_9936])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1962,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | X1 != u1_struct_0(sK3)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_2953,plain,
    ( m1_subset_1(sK6,X0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_1962])).

cnf(c_3755,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1805,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1807,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3342,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1807])).

cnf(c_3350,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3342,c_42,c_2488])).

cnf(c_3351,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3350])).

cnf(c_3356,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3351])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_220,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_8])).

cnf(c_221,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_220])).

cnf(c_1788,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_2340,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1788])).

cnf(c_3191,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_42,c_2488])).

cnf(c_3192,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3191])).

cnf(c_3197,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3192])).

cnf(c_3198,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3197])).

cnf(c_1045,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3015,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1046,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2014,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2287,plain,
    ( X0 != sK6
    | X0 = sK5
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_2533,plain,
    ( sK6 != sK6
    | sK6 = sK5
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2450,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2044,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2449,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_12,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_212,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_213,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_490,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X1 != X2
    | u1_struct_0(X0) != k2_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_213])).

cnf(c_491,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_586,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_587,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_591,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_29])).

cnf(c_592,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_635,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_592,c_18])).

cnf(c_657,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X5) != k2_struct_0(X6) ),
    inference(resolution_lifted,[status(thm)],[c_491,c_635])).

cnf(c_658,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X0) != k2_struct_0(X3) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_702,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X0) != k2_struct_0(X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_658,c_5,c_8])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2254,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK2) != k2_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_702,c_22])).

cnf(c_2255,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_2254])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2345,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK3,sK1,sK4,sK6)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2255,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31,c_30,c_27,c_24])).

cnf(c_2346,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_2345])).

cnf(c_1996,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1907,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_104,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_100,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58621,c_11368,c_10679,c_3755,c_3356,c_3198,c_3197,c_3015,c_2533,c_2488,c_2487,c_2486,c_2450,c_2449,c_2346,c_1996,c_1907,c_104,c_100,c_21,c_23,c_25,c_42,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 27.33/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.33/4.00  
% 27.33/4.00  ------  iProver source info
% 27.33/4.00  
% 27.33/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.33/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.33/4.00  git: non_committed_changes: false
% 27.33/4.00  git: last_make_outside_of_git: false
% 27.33/4.00  
% 27.33/4.00  ------ 
% 27.33/4.00  ------ Parsing...
% 27.33/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.33/4.00  ------ Proving...
% 27.33/4.00  ------ Problem Properties 
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  clauses                                 31
% 27.33/4.00  conjectures                             17
% 27.33/4.00  EPR                                     18
% 27.33/4.00  Horn                                    29
% 27.33/4.00  unary                                   18
% 27.33/4.00  binary                                  4
% 27.33/4.00  lits                                    86
% 27.33/4.00  lits eq                                 10
% 27.33/4.00  fd_pure                                 0
% 27.33/4.00  fd_pseudo                               0
% 27.33/4.00  fd_cond                                 0
% 27.33/4.00  fd_pseudo_cond                          1
% 27.33/4.00  AC symbols                              0
% 27.33/4.00  
% 27.33/4.00  ------ Input Options Time Limit: Unbounded
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  ------ 
% 27.33/4.00  Current options:
% 27.33/4.00  ------ 
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  ------ Proving...
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  % SZS status Theorem for theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  fof(f15,conjecture,(
% 27.33/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f16,negated_conjecture,(
% 27.33/4.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 27.33/4.00    inference(negated_conjecture,[],[f15])).
% 27.33/4.00  
% 27.33/4.00  fof(f34,plain,(
% 27.33/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 27.33/4.00    inference(ennf_transformation,[],[f16])).
% 27.33/4.00  
% 27.33/4.00  fof(f35,plain,(
% 27.33/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.33/4.00    inference(flattening,[],[f34])).
% 27.33/4.00  
% 27.33/4.00  fof(f49,plain,(
% 27.33/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f48,plain,(
% 27.33/4.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f47,plain,(
% 27.33/4.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f46,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f45,plain,(
% 27.33/4.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f44,plain,(
% 27.33/4.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f43,plain,(
% 27.33/4.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f50,plain,(
% 27.33/4.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 27.33/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f49,f48,f47,f46,f45,f44,f43])).
% 27.33/4.00  
% 27.33/4.00  fof(f81,plain,(
% 27.33/4.00    m1_pre_topc(sK3,sK0)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f6,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f21,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f6])).
% 27.33/4.00  
% 27.33/4.00  fof(f59,plain,(
% 27.33/4.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f21])).
% 27.33/4.00  
% 27.33/4.00  fof(f74,plain,(
% 27.33/4.00    l1_pre_topc(sK0)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f5,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f20,plain,(
% 27.33/4.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f5])).
% 27.33/4.00  
% 27.33/4.00  fof(f58,plain,(
% 27.33/4.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f20])).
% 27.33/4.00  
% 27.33/4.00  fof(f4,axiom,(
% 27.33/4.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f19,plain,(
% 27.33/4.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f4])).
% 27.33/4.00  
% 27.33/4.00  fof(f57,plain,(
% 27.33/4.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f19])).
% 27.33/4.00  
% 27.33/4.00  fof(f79,plain,(
% 27.33/4.00    m1_pre_topc(sK2,sK0)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f11,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f28,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f11])).
% 27.33/4.00  
% 27.33/4.00  fof(f67,plain,(
% 27.33/4.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f28])).
% 27.33/4.00  
% 27.33/4.00  fof(f2,axiom,(
% 27.33/4.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f38,plain,(
% 27.33/4.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.33/4.00    inference(nnf_transformation,[],[f2])).
% 27.33/4.00  
% 27.33/4.00  fof(f54,plain,(
% 27.33/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.33/4.00    inference(cnf_transformation,[],[f38])).
% 27.33/4.00  
% 27.33/4.00  fof(f1,axiom,(
% 27.33/4.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f36,plain,(
% 27.33/4.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.33/4.00    inference(nnf_transformation,[],[f1])).
% 27.33/4.00  
% 27.33/4.00  fof(f37,plain,(
% 27.33/4.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.33/4.00    inference(flattening,[],[f36])).
% 27.33/4.00  
% 27.33/4.00  fof(f53,plain,(
% 27.33/4.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f37])).
% 27.33/4.00  
% 27.33/4.00  fof(f12,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f29,plain,(
% 27.33/4.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f12])).
% 27.33/4.00  
% 27.33/4.00  fof(f68,plain,(
% 27.33/4.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f29])).
% 27.33/4.00  
% 27.33/4.00  fof(f85,plain,(
% 27.33/4.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f7,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f22,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f7])).
% 27.33/4.00  
% 27.33/4.00  fof(f60,plain,(
% 27.33/4.00    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f22])).
% 27.33/4.00  
% 27.33/4.00  fof(f8,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f23,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f8])).
% 27.33/4.00  
% 27.33/4.00  fof(f39,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(nnf_transformation,[],[f23])).
% 27.33/4.00  
% 27.33/4.00  fof(f61,plain,(
% 27.33/4.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f39])).
% 27.33/4.00  
% 27.33/4.00  fof(f52,plain,(
% 27.33/4.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.33/4.00    inference(cnf_transformation,[],[f37])).
% 27.33/4.00  
% 27.33/4.00  fof(f91,plain,(
% 27.33/4.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.33/4.00    inference(equality_resolution,[],[f52])).
% 27.33/4.00  
% 27.33/4.00  fof(f9,axiom,(
% 27.33/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f24,plain,(
% 27.33/4.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.33/4.00    inference(ennf_transformation,[],[f9])).
% 27.33/4.00  
% 27.33/4.00  fof(f25,plain,(
% 27.33/4.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.33/4.00    inference(flattening,[],[f24])).
% 27.33/4.00  
% 27.33/4.00  fof(f63,plain,(
% 27.33/4.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f25])).
% 27.33/4.00  
% 27.33/4.00  fof(f10,axiom,(
% 27.33/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f26,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.33/4.00    inference(ennf_transformation,[],[f10])).
% 27.33/4.00  
% 27.33/4.00  fof(f27,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.33/4.00    inference(flattening,[],[f26])).
% 27.33/4.00  
% 27.33/4.00  fof(f40,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.33/4.00    inference(nnf_transformation,[],[f27])).
% 27.33/4.00  
% 27.33/4.00  fof(f41,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.33/4.00    inference(flattening,[],[f40])).
% 27.33/4.00  
% 27.33/4.00  fof(f65,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f41])).
% 27.33/4.00  
% 27.33/4.00  fof(f94,plain,(
% 27.33/4.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.33/4.00    inference(equality_resolution,[],[f65])).
% 27.33/4.00  
% 27.33/4.00  fof(f14,axiom,(
% 27.33/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f32,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.33/4.00    inference(ennf_transformation,[],[f14])).
% 27.33/4.00  
% 27.33/4.00  fof(f33,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.33/4.00    inference(flattening,[],[f32])).
% 27.33/4.00  
% 27.33/4.00  fof(f42,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.33/4.00    inference(nnf_transformation,[],[f33])).
% 27.33/4.00  
% 27.33/4.00  fof(f71,plain,(
% 27.33/4.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f42])).
% 27.33/4.00  
% 27.33/4.00  fof(f96,plain,(
% 27.33/4.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.33/4.00    inference(equality_resolution,[],[f71])).
% 27.33/4.00  
% 27.33/4.00  fof(f83,plain,(
% 27.33/4.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f82,plain,(
% 27.33/4.00    v1_funct_1(sK4)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f13,axiom,(
% 27.33/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f30,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.33/4.00    inference(ennf_transformation,[],[f13])).
% 27.33/4.00  
% 27.33/4.00  fof(f31,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.33/4.00    inference(flattening,[],[f30])).
% 27.33/4.00  
% 27.33/4.00  fof(f69,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f31])).
% 27.33/4.00  
% 27.33/4.00  fof(f3,axiom,(
% 27.33/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 27.33/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f17,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.33/4.00    inference(ennf_transformation,[],[f3])).
% 27.33/4.00  
% 27.33/4.00  fof(f18,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.33/4.00    inference(flattening,[],[f17])).
% 27.33/4.00  
% 27.33/4.00  fof(f56,plain,(
% 27.33/4.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f18])).
% 27.33/4.00  
% 27.33/4.00  fof(f89,plain,(
% 27.33/4.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f72,plain,(
% 27.33/4.00    ~v2_struct_0(sK0)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f73,plain,(
% 27.33/4.00    v2_pre_topc(sK0)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f75,plain,(
% 27.33/4.00    ~v2_struct_0(sK1)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f76,plain,(
% 27.33/4.00    v2_pre_topc(sK1)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f77,plain,(
% 27.33/4.00    l1_pre_topc(sK1)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f78,plain,(
% 27.33/4.00    ~v2_struct_0(sK2)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f80,plain,(
% 27.33/4.00    ~v2_struct_0(sK3)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f84,plain,(
% 27.33/4.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f87,plain,(
% 27.33/4.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f51,plain,(
% 27.33/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.33/4.00    inference(cnf_transformation,[],[f37])).
% 27.33/4.00  
% 27.33/4.00  fof(f92,plain,(
% 27.33/4.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.33/4.00    inference(equality_resolution,[],[f51])).
% 27.33/4.00  
% 27.33/4.00  fof(f90,plain,(
% 27.33/4.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f88,plain,(
% 27.33/4.00    sK5 = sK6),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  fof(f86,plain,(
% 27.33/4.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 27.33/4.00    inference(cnf_transformation,[],[f50])).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1055,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 27.33/4.00      | r1_tmap_1(X4,X5,X6,X7)
% 27.33/4.00      | X4 != X0
% 27.33/4.00      | X5 != X1
% 27.33/4.00      | X6 != X2
% 27.33/4.00      | X7 != X3 ),
% 27.33/4.00      theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_18301,plain,
% 27.33/4.00      ( r1_tmap_1(X0,X1,X2,X3)
% 27.33/4.00      | ~ r1_tmap_1(sK3,X4,sK4,sK6)
% 27.33/4.00      | X1 != X4
% 27.33/4.00      | X3 != sK6
% 27.33/4.00      | X2 != sK4
% 27.33/4.00      | X0 != sK3 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1055]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_30227,plain,
% 27.33/4.00      ( r1_tmap_1(X0,X1,sK4,X2)
% 27.33/4.00      | ~ r1_tmap_1(sK3,X3,sK4,sK6)
% 27.33/4.00      | X1 != X3
% 27.33/4.00      | X2 != sK6
% 27.33/4.00      | X0 != sK3
% 27.33/4.00      | sK4 != sK4 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_18301]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_57337,plain,
% 27.33/4.00      ( r1_tmap_1(X0,X1,sK4,sK5)
% 27.33/4.00      | ~ r1_tmap_1(sK3,X2,sK4,sK6)
% 27.33/4.00      | X1 != X2
% 27.33/4.00      | X0 != sK3
% 27.33/4.00      | sK5 != sK6
% 27.33/4.00      | sK4 != sK4 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_30227]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_58619,plain,
% 27.33/4.00      ( ~ r1_tmap_1(sK3,X0,sK4,sK6)
% 27.33/4.00      | r1_tmap_1(sK3,X1,sK4,sK5)
% 27.33/4.00      | X1 != X0
% 27.33/4.00      | sK5 != sK6
% 27.33/4.00      | sK4 != sK4
% 27.33/4.00      | sK3 != sK3 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_57337]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_58621,plain,
% 27.33/4.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK6)
% 27.33/4.00      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 27.33/4.00      | sK5 != sK6
% 27.33/4.00      | sK4 != sK4
% 27.33/4.00      | sK1 != sK1
% 27.33/4.00      | sK3 != sK3 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_58619]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_30,negated_conjecture,
% 27.33/4.00      ( m1_pre_topc(sK3,sK0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1798,plain,
% 27.33/4.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_8,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f59]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1808,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X1) != iProver_top
% 27.33/4.00      | l1_pre_topc(X1) != iProver_top
% 27.33/4.00      | l1_pre_topc(X0) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3104,plain,
% 27.33/4.00      ( l1_pre_topc(sK0) != iProver_top
% 27.33/4.00      | l1_pre_topc(sK3) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_1798,c_1808]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_37,negated_conjecture,
% 27.33/4.00      ( l1_pre_topc(sK0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f74]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_42,plain,
% 27.33/4.00      ( l1_pre_topc(sK0) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2485,plain,
% 27.33/4.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 27.33/4.00      inference(resolution,[status(thm)],[c_8,c_30]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2486,plain,
% 27.33/4.00      ( l1_pre_topc(sK0) != iProver_top
% 27.33/4.00      | l1_pre_topc(sK3) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_2485]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3768,plain,
% 27.33/4.00      ( l1_pre_topc(sK3) = iProver_top ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_3104,c_42,c_2486]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_7,plain,
% 27.33/4.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f58]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_6,plain,
% 27.33/4.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f57]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_475,plain,
% 27.33/4.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.33/4.00      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1787,plain,
% 27.33/4.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 27.33/4.00      | l1_pre_topc(X0) != iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3772,plain,
% 27.33/4.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_3768,c_1787]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_32,negated_conjecture,
% 27.33/4.00      ( m1_pre_topc(sK2,sK0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1796,plain,
% 27.33/4.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3105,plain,
% 27.33/4.00      ( l1_pre_topc(sK0) != iProver_top
% 27.33/4.00      | l1_pre_topc(sK2) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_1796,c_1808]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2487,plain,
% 27.33/4.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 27.33/4.00      inference(resolution,[status(thm)],[c_8,c_32]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2488,plain,
% 27.33/4.00      ( l1_pre_topc(sK0) != iProver_top
% 27.33/4.00      | l1_pre_topc(sK2) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_2487]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3875,plain,
% 27.33/4.00      ( l1_pre_topc(sK2) = iProver_top ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_3105,c_42,c_2488]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3879,plain,
% 27.33/4.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_3875,c_1787]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_16,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f67]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1806,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X1) != iProver_top
% 27.33/4.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 27.33/4.00      | l1_pre_topc(X1) != iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_10711,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 27.33/4.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 27.33/4.00      | l1_pre_topc(sK2) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_3879,c_1806]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_11348,plain,
% 27.33/4.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_10711,c_42,c_2488]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_11349,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 27.33/4.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_11348]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_4,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f54]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1810,plain,
% 27.33/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.33/4.00      | r1_tarski(X0,X1) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_11358,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 27.33/4.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_11349,c_1810]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_11368,plain,
% 27.33/4.00      ( m1_pre_topc(sK3,sK2) != iProver_top
% 27.33/4.00      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_3772,c_11358]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9228,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 27.33/4.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 27.33/4.00      | l1_pre_topc(sK3) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_3772,c_1806]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9747,plain,
% 27.33/4.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK3) != iProver_top ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_9228,c_42,c_2486]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9748,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 27.33/4.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_9747]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9756,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 27.33/4.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_9748,c_1810]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_0,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.33/4.00      inference(cnf_transformation,[],[f53]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1813,plain,
% 27.33/4.00      ( X0 = X1
% 27.33/4.00      | r1_tarski(X0,X1) != iProver_top
% 27.33/4.00      | r1_tarski(X1,X0) != iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9936,plain,
% 27.33/4.00      ( u1_struct_0(X0) = k2_struct_0(sK3)
% 27.33/4.00      | m1_pre_topc(X0,sK3) != iProver_top
% 27.33/4.00      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_9756,c_1813]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_10679,plain,
% 27.33/4.00      ( u1_struct_0(sK2) = k2_struct_0(sK3)
% 27.33/4.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 27.33/4.00      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_3879,c_9936]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1048,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.33/4.00      theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1962,plain,
% 27.33/4.00      ( m1_subset_1(X0,X1)
% 27.33/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 27.33/4.00      | X1 != u1_struct_0(sK3)
% 27.33/4.00      | X0 != sK5 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1048]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2953,plain,
% 27.33/4.00      ( m1_subset_1(sK6,X0)
% 27.33/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 27.33/4.00      | X0 != u1_struct_0(sK3)
% 27.33/4.00      | sK6 != sK5 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1962]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3755,plain,
% 27.33/4.00      ( m1_subset_1(sK6,u1_struct_0(sK3))
% 27.33/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 27.33/4.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 27.33/4.00      | sK6 != sK5 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2953]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_17,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1805,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X0) = iProver_top
% 27.33/4.00      | l1_pre_topc(X0) != iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_26,negated_conjecture,
% 27.33/4.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 27.33/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f60]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1807,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X1) = iProver_top
% 27.33/4.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 27.33/4.00      | l1_pre_topc(X1) != iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3342,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) = iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK3) != iProver_top
% 27.33/4.00      | l1_pre_topc(sK2) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_26,c_1807]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3350,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK2) = iProver_top ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_3342,c_42,c_2488]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3351,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) = iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK3) != iProver_top ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_3350]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3356,plain,
% 27.33/4.00      ( m1_pre_topc(sK3,sK2) = iProver_top
% 27.33/4.00      | l1_pre_topc(sK3) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_1805,c_3351]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_11,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.33/4.00      | ~ l1_pre_topc(X0)
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f61]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_220,plain,
% 27.33/4.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.33/4.00      | ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_11,c_8]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_221,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_220]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1788,plain,
% 27.33/4.00      ( m1_pre_topc(X0,X1) != iProver_top
% 27.33/4.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 27.33/4.00      | l1_pre_topc(X1) != iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2340,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK3) = iProver_top
% 27.33/4.00      | l1_pre_topc(sK2) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_26,c_1788]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3191,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_2340,c_42,c_2488]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3192,plain,
% 27.33/4.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 27.33/4.00      | m1_pre_topc(X0,sK3) = iProver_top ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_3191]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3197,plain,
% 27.33/4.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 27.33/4.00      | l1_pre_topc(sK2) != iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_1805,c_3192]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3198,plain,
% 27.33/4.00      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 27.33/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_3197]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1045,plain,( X0 = X0 ),theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3015,plain,
% 27.33/4.00      ( sK4 = sK4 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1045]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1046,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2014,plain,
% 27.33/4.00      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1046]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2287,plain,
% 27.33/4.00      ( X0 != sK6 | X0 = sK5 | sK5 != sK6 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2014]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2533,plain,
% 27.33/4.00      ( sK6 != sK6 | sK6 = sK5 | sK5 != sK6 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2287]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1,plain,
% 27.33/4.00      ( r1_tarski(X0,X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2450,plain,
% 27.33/4.00      ( r1_tarski(sK3,sK3) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2044,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | X0 = sK3 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2449,plain,
% 27.33/4.00      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2044]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_12,plain,
% 27.33/4.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 27.33/4.00      | ~ l1_pre_topc(X0)
% 27.33/4.00      | ~ v2_pre_topc(X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f63]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_14,plain,
% 27.33/4.00      ( v1_tsep_1(X0,X1)
% 27.33/4.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 27.33/4.00      | ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f94]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_212,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 27.33/4.00      | v1_tsep_1(X0,X1)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X1) ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_14,c_16]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_213,plain,
% 27.33/4.00      ( v1_tsep_1(X0,X1)
% 27.33/4.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 27.33/4.00      | ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X1) ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_212]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_490,plain,
% 27.33/4.00      ( v1_tsep_1(X0,X1)
% 27.33/4.00      | ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | X1 != X2
% 27.33/4.00      | u1_struct_0(X0) != k2_struct_0(X2) ),
% 27.33/4.00      inference(resolution_lifted,[status(thm)],[c_12,c_213]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_491,plain,
% 27.33/4.00      ( v1_tsep_1(X0,X1)
% 27.33/4.00      | ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 27.33/4.00      inference(unflattening,[status(thm)],[c_490]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_19,plain,
% 27.33/4.00      ( r1_tmap_1(X0,X1,X2,X3)
% 27.33/4.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 27.33/4.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 27.33/4.00      | ~ v1_tsep_1(X4,X0)
% 27.33/4.00      | ~ m1_pre_topc(X4,X5)
% 27.33/4.00      | ~ m1_pre_topc(X4,X0)
% 27.33/4.00      | ~ m1_pre_topc(X0,X5)
% 27.33/4.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 27.33/4.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X5)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X4)
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | ~ v1_funct_1(X2)
% 27.33/4.00      | ~ l1_pre_topc(X5)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X5)
% 27.33/4.00      | ~ v2_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_28,negated_conjecture,
% 27.33/4.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 27.33/4.00      inference(cnf_transformation,[],[f83]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_586,plain,
% 27.33/4.00      ( r1_tmap_1(X0,X1,X2,X3)
% 27.33/4.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 27.33/4.00      | ~ v1_tsep_1(X4,X0)
% 27.33/4.00      | ~ m1_pre_topc(X4,X5)
% 27.33/4.00      | ~ m1_pre_topc(X4,X0)
% 27.33/4.00      | ~ m1_pre_topc(X0,X5)
% 27.33/4.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 27.33/4.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X5)
% 27.33/4.00      | v2_struct_0(X4)
% 27.33/4.00      | ~ v1_funct_1(X2)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X5)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X5)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 27.33/4.00      | sK4 != X2 ),
% 27.33/4.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_587,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ v1_tsep_1(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X0,X2)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | ~ v1_funct_1(sK4)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.33/4.00      inference(unflattening,[status(thm)],[c_586]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_29,negated_conjecture,
% 27.33/4.00      ( v1_funct_1(sK4) ),
% 27.33/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_591,plain,
% 27.33/4.00      ( v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X0,X2)
% 27.33/4.00      | ~ v1_tsep_1(X0,X3)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_587,c_29]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_592,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ v1_tsep_1(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X0,X2)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_591]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_18,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ m1_pre_topc(X2,X0)
% 27.33/4.00      | m1_pre_topc(X2,X1)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f69]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_635,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ v1_tsep_1(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 27.33/4.00      inference(forward_subsumption_resolution,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_592,c_18]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_657,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ m1_pre_topc(X5,X6)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | ~ l1_pre_topc(X6)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X6)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | X0 != X5
% 27.33/4.00      | X3 != X6
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 27.33/4.00      | u1_struct_0(X5) != k2_struct_0(X6) ),
% 27.33/4.00      inference(resolution_lifted,[status(thm)],[c_491,c_635]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_658,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ l1_pre_topc(X3)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X3)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 27.33/4.00      | u1_struct_0(X0) != k2_struct_0(X3) ),
% 27.33/4.00      inference(unflattening,[status(thm)],[c_657]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_5,plain,
% 27.33/4.00      ( ~ m1_pre_topc(X0,X1)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | v2_pre_topc(X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f56]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_702,plain,
% 27.33/4.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 27.33/4.00      | r1_tmap_1(X3,X1,sK4,X4)
% 27.33/4.00      | ~ m1_pre_topc(X0,X3)
% 27.33/4.00      | ~ m1_pre_topc(X3,X2)
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 27.33/4.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 27.33/4.00      | v2_struct_0(X0)
% 27.33/4.00      | v2_struct_0(X1)
% 27.33/4.00      | v2_struct_0(X2)
% 27.33/4.00      | v2_struct_0(X3)
% 27.33/4.00      | ~ l1_pre_topc(X1)
% 27.33/4.00      | ~ l1_pre_topc(X2)
% 27.33/4.00      | ~ v2_pre_topc(X1)
% 27.33/4.00      | ~ v2_pre_topc(X2)
% 27.33/4.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 27.33/4.00      | u1_struct_0(X0) != k2_struct_0(X3) ),
% 27.33/4.00      inference(forward_subsumption_resolution,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_658,c_5,c_8]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_22,negated_conjecture,
% 27.33/4.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 27.33/4.00      inference(cnf_transformation,[],[f89]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2254,plain,
% 27.33/4.00      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 27.33/4.00      | ~ m1_pre_topc(sK2,sK3)
% 27.33/4.00      | ~ m1_pre_topc(sK3,sK0)
% 27.33/4.00      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 27.33/4.00      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 27.33/4.00      | v2_struct_0(sK0)
% 27.33/4.00      | v2_struct_0(sK2)
% 27.33/4.00      | v2_struct_0(sK1)
% 27.33/4.00      | v2_struct_0(sK3)
% 27.33/4.00      | ~ l1_pre_topc(sK0)
% 27.33/4.00      | ~ l1_pre_topc(sK1)
% 27.33/4.00      | ~ v2_pre_topc(sK0)
% 27.33/4.00      | ~ v2_pre_topc(sK1)
% 27.33/4.00      | u1_struct_0(sK2) != k2_struct_0(sK3)
% 27.33/4.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 27.33/4.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 27.33/4.00      inference(resolution,[status(thm)],[c_702,c_22]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2255,plain,
% 27.33/4.00      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 27.33/4.00      | ~ m1_pre_topc(sK2,sK3)
% 27.33/4.00      | ~ m1_pre_topc(sK3,sK0)
% 27.33/4.00      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 27.33/4.00      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 27.33/4.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 27.33/4.00      | v2_struct_0(sK0)
% 27.33/4.00      | v2_struct_0(sK2)
% 27.33/4.00      | v2_struct_0(sK1)
% 27.33/4.00      | v2_struct_0(sK3)
% 27.33/4.00      | ~ l1_pre_topc(sK0)
% 27.33/4.00      | ~ l1_pre_topc(sK1)
% 27.33/4.00      | ~ v2_pre_topc(sK0)
% 27.33/4.00      | ~ v2_pre_topc(sK1)
% 27.33/4.00      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 27.33/4.00      inference(equality_resolution_simp,[status(thm)],[c_2254]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_39,negated_conjecture,
% 27.33/4.00      ( ~ v2_struct_0(sK0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_38,negated_conjecture,
% 27.33/4.00      ( v2_pre_topc(sK0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f73]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_36,negated_conjecture,
% 27.33/4.00      ( ~ v2_struct_0(sK1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f75]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_35,negated_conjecture,
% 27.33/4.00      ( v2_pre_topc(sK1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f76]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_34,negated_conjecture,
% 27.33/4.00      ( l1_pre_topc(sK1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f77]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_33,negated_conjecture,
% 27.33/4.00      ( ~ v2_struct_0(sK2) ),
% 27.33/4.00      inference(cnf_transformation,[],[f78]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_31,negated_conjecture,
% 27.33/4.00      ( ~ v2_struct_0(sK3) ),
% 27.33/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_27,negated_conjecture,
% 27.33/4.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 27.33/4.00      inference(cnf_transformation,[],[f84]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_24,negated_conjecture,
% 27.33/4.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 27.33/4.00      inference(cnf_transformation,[],[f87]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2345,plain,
% 27.33/4.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 27.33/4.00      | ~ m1_pre_topc(sK2,sK3)
% 27.33/4.00      | r1_tmap_1(sK3,sK1,sK4,sK6)
% 27.33/4.00      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 27.33/4.00      inference(global_propositional_subsumption,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_2255,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_31,c_30,
% 27.33/4.00                 c_27,c_24]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2346,plain,
% 27.33/4.00      ( r1_tmap_1(sK3,sK1,sK4,sK6)
% 27.33/4.00      | ~ m1_pre_topc(sK2,sK3)
% 27.33/4.00      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 27.33/4.00      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_2345]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1996,plain,
% 27.33/4.00      ( sK6 = sK6 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1045]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1907,plain,
% 27.33/4.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1045]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_104,plain,
% 27.33/4.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2,plain,
% 27.33/4.00      ( r1_tarski(X0,X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f92]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_100,plain,
% 27.33/4.00      ( r1_tarski(sK1,sK1) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_21,negated_conjecture,
% 27.33/4.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 27.33/4.00      inference(cnf_transformation,[],[f90]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_23,negated_conjecture,
% 27.33/4.00      ( sK5 = sK6 ),
% 27.33/4.00      inference(cnf_transformation,[],[f88]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_25,negated_conjecture,
% 27.33/4.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 27.33/4.00      inference(cnf_transformation,[],[f86]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(contradiction,plain,
% 27.33/4.00      ( $false ),
% 27.33/4.00      inference(minisat,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_58621,c_11368,c_10679,c_3755,c_3356,c_3198,c_3197,
% 27.33/4.00                 c_3015,c_2533,c_2488,c_2487,c_2486,c_2450,c_2449,c_2346,
% 27.33/4.00                 c_1996,c_1907,c_104,c_100,c_21,c_23,c_25,c_42,c_37]) ).
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  ------                               Statistics
% 27.33/4.00  
% 27.33/4.00  ------ Selected
% 27.33/4.00  
% 27.33/4.00  total_time:                             3.008
% 27.33/4.00  
%------------------------------------------------------------------------------
