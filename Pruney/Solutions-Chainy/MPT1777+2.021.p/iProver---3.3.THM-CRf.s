%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:29 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  232 (1619 expanded)
%              Number of clauses        :  141 ( 425 expanded)
%              Number of leaves         :   23 ( 676 expanded)
%              Depth                    :   26
%              Number of atoms          : 1281 (21518 expanded)
%              Number of equality atoms :  407 (3365 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f42])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f53,f52,f51,f50,f49,f48,f47])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f15,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f85,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_922,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1535,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_940,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1519,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_2448,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1519])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2653,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2448,c_40])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_383,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_913,plain,
    ( ~ l1_pre_topc(X0_54)
    | k2_struct_0(X0_54) = u1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_1544,plain,
    ( k2_struct_0(X0_54) = u1_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_3081,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2653,c_1544])).

cnf(c_9,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_936,plain,
    ( v3_pre_topc(k2_struct_0(X0_54),X0_54)
    | ~ v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1523,plain,
    ( v3_pre_topc(k2_struct_0(X0_54),X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_3375,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3081,c_1523])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_941,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1518,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_941])).

cnf(c_2356,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1518])).

cnf(c_4776,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3375,c_39,c_40,c_2356,c_2448])).

cnf(c_14,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_934,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1525,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_935,plain,
    ( ~ v3_pre_topc(X0_55,X0_54)
    | v3_pre_topc(X0_55,X1_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1524,plain,
    ( v3_pre_topc(X0_55,X0_54) != iProver_top
    | v3_pre_topc(X0_55,X1_54) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1522,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_1659,plain,
    ( v3_pre_topc(X0_55,X0_54) != iProver_top
    | v3_pre_topc(X0_55,X1_54) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1524,c_1522])).

cnf(c_4681,plain,
    ( v3_pre_topc(u1_struct_0(X0_54),X1_54) != iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),X2_54) = iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1659])).

cnf(c_6136,plain,
    ( v3_pre_topc(u1_struct_0(X0_54),X1_54) != iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),X2_54) = iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4681,c_1519])).

cnf(c_6141,plain,
    ( v3_pre_topc(u1_struct_0(sK2),X0_54) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4776,c_6136])).

cnf(c_8721,plain,
    ( m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v3_pre_topc(u1_struct_0(sK2),X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6141,c_40,c_2448])).

cnf(c_8722,plain,
    ( v3_pre_topc(u1_struct_0(sK2),X0_54) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_8721])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_930,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1529,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_929,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1588,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1529,c_929])).

cnf(c_12,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_200,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_201,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_488,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_489,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_493,plain,
    ( ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_27])).

cnf(c_494,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_537,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_494,c_16])).

cnf(c_560,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X5),X6)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_201,c_537])).

cnf(c_561,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_605,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_561,c_4,c_1])).

cnf(c_912,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
    | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
    | ~ v3_pre_topc(u1_struct_0(X0_54),X3_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_1545,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK3)
    | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X2_54),X1_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_2346,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK3)
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1545])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5392,plain,
    ( l1_pre_topc(X2_54) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | u1_struct_0(X0_54) != u1_struct_0(sK3)
    | v2_pre_topc(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2346,c_41,c_42,c_43])).

cnf(c_5393,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK3)
    | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_5392])).

cnf(c_5410,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5393])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10435,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5410,c_46,c_50])).

cnf(c_10436,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_10435])).

cnf(c_10452,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_10436])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_54,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_928,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1530,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_1569,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1530,c_929])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_933,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1526,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_924,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1533,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_2447,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1519])).

cnf(c_2598,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2447,c_40])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_942,plain,
    ( ~ l1_pre_topc(X0_54)
    | ~ v1_pre_topc(X0_54)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1517,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = X0_54
    | l1_pre_topc(X0_54) != iProver_top
    | v1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_2603,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_1517])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_926,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_939,plain,
    ( v2_struct_0(X0_54)
    | ~ l1_pre_topc(X0_54)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1520,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_2514,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_1520])).

cnf(c_2816,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_40,c_44,c_2448,c_2514])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_210,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_4])).

cnf(c_211,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_914,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(X2_54,X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(X3_54)
    | g1_pre_topc(u1_struct_0(X3_54),u1_pre_topc(X3_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) ),
    inference(subtyping,[status(esa)],[c_211])).

cnf(c_1543,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != g1_pre_topc(u1_struct_0(X3_54),u1_pre_topc(X3_54))
    | m1_pre_topc(X3_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_914])).

cnf(c_3467,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
    | m1_pre_topc(X1_54,X2_54) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_1543])).

cnf(c_3816,plain,
    ( l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X1_54,X2_54) = iProver_top
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3467,c_40,c_2448])).

cnf(c_3817,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
    | m1_pre_topc(X1_54,X2_54) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3816])).

cnf(c_3826,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
    | g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) != sK3
    | m1_pre_topc(X0_54,X1_54) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_3817])).

cnf(c_3905,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
    | m1_pre_topc(sK2,X0_54) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_3826])).

cnf(c_3992,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_54) = iProver_top
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3905,c_40,c_2448])).

cnf(c_3993,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
    | m1_pre_topc(sK2,X0_54) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3992])).

cnf(c_4003,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_3993])).

cnf(c_4131,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4003,c_40,c_2447])).

cnf(c_4132,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4131])).

cnf(c_4137,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_4132])).

cnf(c_10455,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10452,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1569,c_2448,c_4137])).

cnf(c_10461,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8722,c_10455])).

cnf(c_3465,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK2) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_1543])).

cnf(c_3628,plain,
    ( l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | m1_pre_topc(X1_54,sK2) = iProver_top
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3465,c_40,c_2448])).

cnf(c_3629,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
    | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
    | m1_pre_topc(X0_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,sK2) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3628])).

cnf(c_3640,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
    | g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) != sK3
    | m1_pre_topc(X0_54,sK2) = iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_3629])).

cnf(c_3717,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_3640])).

cnf(c_4265,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | m1_pre_topc(sK3,sK2) = iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3717,c_40,c_2447])).

cnf(c_4266,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4265])).

cnf(c_4276,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_4266])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10461,c_4276,c_4137,c_2448,c_2447,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.30/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/0.99  
% 3.30/0.99  ------  iProver source info
% 3.30/0.99  
% 3.30/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.30/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/0.99  git: non_committed_changes: false
% 3.30/0.99  git: last_make_outside_of_git: false
% 3.30/0.99  
% 3.30/0.99  ------ 
% 3.30/0.99  
% 3.30/0.99  ------ Input Options
% 3.30/0.99  
% 3.30/0.99  --out_options                           all
% 3.30/0.99  --tptp_safe_out                         true
% 3.30/0.99  --problem_path                          ""
% 3.30/0.99  --include_path                          ""
% 3.30/0.99  --clausifier                            res/vclausify_rel
% 3.30/0.99  --clausifier_options                    --mode clausify
% 3.30/0.99  --stdin                                 false
% 3.30/0.99  --stats_out                             all
% 3.30/0.99  
% 3.30/0.99  ------ General Options
% 3.30/0.99  
% 3.30/0.99  --fof                                   false
% 3.30/0.99  --time_out_real                         305.
% 3.30/0.99  --time_out_virtual                      -1.
% 3.30/0.99  --symbol_type_check                     false
% 3.30/0.99  --clausify_out                          false
% 3.30/0.99  --sig_cnt_out                           false
% 3.30/0.99  --trig_cnt_out                          false
% 3.30/0.99  --trig_cnt_out_tolerance                1.
% 3.30/0.99  --trig_cnt_out_sk_spl                   false
% 3.30/0.99  --abstr_cl_out                          false
% 3.30/0.99  
% 3.30/0.99  ------ Global Options
% 3.30/0.99  
% 3.30/0.99  --schedule                              default
% 3.30/0.99  --add_important_lit                     false
% 3.30/0.99  --prop_solver_per_cl                    1000
% 3.30/0.99  --min_unsat_core                        false
% 3.30/0.99  --soft_assumptions                      false
% 3.30/0.99  --soft_lemma_size                       3
% 3.30/0.99  --prop_impl_unit_size                   0
% 3.30/0.99  --prop_impl_unit                        []
% 3.30/0.99  --share_sel_clauses                     true
% 3.30/0.99  --reset_solvers                         false
% 3.30/0.99  --bc_imp_inh                            [conj_cone]
% 3.30/0.99  --conj_cone_tolerance                   3.
% 3.30/0.99  --extra_neg_conj                        none
% 3.30/0.99  --large_theory_mode                     true
% 3.30/0.99  --prolific_symb_bound                   200
% 3.30/0.99  --lt_threshold                          2000
% 3.30/0.99  --clause_weak_htbl                      true
% 3.30/0.99  --gc_record_bc_elim                     false
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing Options
% 3.30/0.99  
% 3.30/0.99  --preprocessing_flag                    true
% 3.30/0.99  --time_out_prep_mult                    0.1
% 3.30/0.99  --splitting_mode                        input
% 3.30/0.99  --splitting_grd                         true
% 3.30/0.99  --splitting_cvd                         false
% 3.30/0.99  --splitting_cvd_svl                     false
% 3.30/0.99  --splitting_nvd                         32
% 3.30/0.99  --sub_typing                            true
% 3.30/0.99  --prep_gs_sim                           true
% 3.30/0.99  --prep_unflatten                        true
% 3.30/0.99  --prep_res_sim                          true
% 3.30/0.99  --prep_upred                            true
% 3.30/0.99  --prep_sem_filter                       exhaustive
% 3.30/0.99  --prep_sem_filter_out                   false
% 3.30/0.99  --pred_elim                             true
% 3.30/0.99  --res_sim_input                         true
% 3.30/0.99  --eq_ax_congr_red                       true
% 3.30/0.99  --pure_diseq_elim                       true
% 3.30/0.99  --brand_transform                       false
% 3.30/0.99  --non_eq_to_eq                          false
% 3.30/0.99  --prep_def_merge                        true
% 3.30/0.99  --prep_def_merge_prop_impl              false
% 3.30/0.99  --prep_def_merge_mbd                    true
% 3.30/0.99  --prep_def_merge_tr_red                 false
% 3.30/0.99  --prep_def_merge_tr_cl                  false
% 3.30/0.99  --smt_preprocessing                     true
% 3.30/0.99  --smt_ac_axioms                         fast
% 3.30/0.99  --preprocessed_out                      false
% 3.30/0.99  --preprocessed_stats                    false
% 3.30/0.99  
% 3.30/0.99  ------ Abstraction refinement Options
% 3.30/0.99  
% 3.30/0.99  --abstr_ref                             []
% 3.30/0.99  --abstr_ref_prep                        false
% 3.30/0.99  --abstr_ref_until_sat                   false
% 3.30/0.99  --abstr_ref_sig_restrict                funpre
% 3.30/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.99  --abstr_ref_under                       []
% 3.30/0.99  
% 3.30/0.99  ------ SAT Options
% 3.30/0.99  
% 3.30/0.99  --sat_mode                              false
% 3.30/0.99  --sat_fm_restart_options                ""
% 3.30/0.99  --sat_gr_def                            false
% 3.30/0.99  --sat_epr_types                         true
% 3.30/0.99  --sat_non_cyclic_types                  false
% 3.30/0.99  --sat_finite_models                     false
% 3.30/0.99  --sat_fm_lemmas                         false
% 3.30/0.99  --sat_fm_prep                           false
% 3.30/0.99  --sat_fm_uc_incr                        true
% 3.30/0.99  --sat_out_model                         small
% 3.30/0.99  --sat_out_clauses                       false
% 3.30/0.99  
% 3.30/0.99  ------ QBF Options
% 3.30/0.99  
% 3.30/0.99  --qbf_mode                              false
% 3.30/0.99  --qbf_elim_univ                         false
% 3.30/0.99  --qbf_dom_inst                          none
% 3.30/0.99  --qbf_dom_pre_inst                      false
% 3.30/0.99  --qbf_sk_in                             false
% 3.30/0.99  --qbf_pred_elim                         true
% 3.30/0.99  --qbf_split                             512
% 3.30/0.99  
% 3.30/0.99  ------ BMC1 Options
% 3.30/0.99  
% 3.30/0.99  --bmc1_incremental                      false
% 3.30/0.99  --bmc1_axioms                           reachable_all
% 3.30/0.99  --bmc1_min_bound                        0
% 3.30/0.99  --bmc1_max_bound                        -1
% 3.30/0.99  --bmc1_max_bound_default                -1
% 3.30/0.99  --bmc1_symbol_reachability              true
% 3.30/0.99  --bmc1_property_lemmas                  false
% 3.30/0.99  --bmc1_k_induction                      false
% 3.30/0.99  --bmc1_non_equiv_states                 false
% 3.30/0.99  --bmc1_deadlock                         false
% 3.30/0.99  --bmc1_ucm                              false
% 3.30/0.99  --bmc1_add_unsat_core                   none
% 3.30/0.99  --bmc1_unsat_core_children              false
% 3.30/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.99  --bmc1_out_stat                         full
% 3.30/0.99  --bmc1_ground_init                      false
% 3.30/0.99  --bmc1_pre_inst_next_state              false
% 3.30/0.99  --bmc1_pre_inst_state                   false
% 3.30/0.99  --bmc1_pre_inst_reach_state             false
% 3.30/0.99  --bmc1_out_unsat_core                   false
% 3.30/0.99  --bmc1_aig_witness_out                  false
% 3.30/0.99  --bmc1_verbose                          false
% 3.30/0.99  --bmc1_dump_clauses_tptp                false
% 3.30/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.99  --bmc1_dump_file                        -
% 3.30/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.99  --bmc1_ucm_extend_mode                  1
% 3.30/0.99  --bmc1_ucm_init_mode                    2
% 3.30/0.99  --bmc1_ucm_cone_mode                    none
% 3.30/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.99  --bmc1_ucm_relax_model                  4
% 3.30/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.99  --bmc1_ucm_layered_model                none
% 3.30/0.99  --bmc1_ucm_max_lemma_size               10
% 3.30/0.99  
% 3.30/0.99  ------ AIG Options
% 3.30/0.99  
% 3.30/0.99  --aig_mode                              false
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation Options
% 3.30/0.99  
% 3.30/0.99  --instantiation_flag                    true
% 3.30/0.99  --inst_sos_flag                         false
% 3.30/0.99  --inst_sos_phase                        true
% 3.30/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel_side                     num_symb
% 3.30/0.99  --inst_solver_per_active                1400
% 3.30/0.99  --inst_solver_calls_frac                1.
% 3.30/0.99  --inst_passive_queue_type               priority_queues
% 3.30/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.99  --inst_passive_queues_freq              [25;2]
% 3.30/0.99  --inst_dismatching                      true
% 3.30/0.99  --inst_eager_unprocessed_to_passive     true
% 3.30/0.99  --inst_prop_sim_given                   true
% 3.30/0.99  --inst_prop_sim_new                     false
% 3.30/0.99  --inst_subs_new                         false
% 3.30/0.99  --inst_eq_res_simp                      false
% 3.30/0.99  --inst_subs_given                       false
% 3.30/0.99  --inst_orphan_elimination               true
% 3.30/0.99  --inst_learning_loop_flag               true
% 3.30/0.99  --inst_learning_start                   3000
% 3.30/0.99  --inst_learning_factor                  2
% 3.30/0.99  --inst_start_prop_sim_after_learn       3
% 3.30/0.99  --inst_sel_renew                        solver
% 3.30/0.99  --inst_lit_activity_flag                true
% 3.30/0.99  --inst_restr_to_given                   false
% 3.30/0.99  --inst_activity_threshold               500
% 3.30/0.99  --inst_out_proof                        true
% 3.30/0.99  
% 3.30/0.99  ------ Resolution Options
% 3.30/0.99  
% 3.30/0.99  --resolution_flag                       true
% 3.30/0.99  --res_lit_sel                           adaptive
% 3.30/0.99  --res_lit_sel_side                      none
% 3.30/0.99  --res_ordering                          kbo
% 3.30/0.99  --res_to_prop_solver                    active
% 3.30/0.99  --res_prop_simpl_new                    false
% 3.30/0.99  --res_prop_simpl_given                  true
% 3.30/0.99  --res_passive_queue_type                priority_queues
% 3.30/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.99  --res_passive_queues_freq               [15;5]
% 3.30/0.99  --res_forward_subs                      full
% 3.30/0.99  --res_backward_subs                     full
% 3.30/0.99  --res_forward_subs_resolution           true
% 3.30/0.99  --res_backward_subs_resolution          true
% 3.30/0.99  --res_orphan_elimination                true
% 3.30/0.99  --res_time_limit                        2.
% 3.30/0.99  --res_out_proof                         true
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Options
% 3.30/0.99  
% 3.30/0.99  --superposition_flag                    true
% 3.30/0.99  --sup_passive_queue_type                priority_queues
% 3.30/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.99  --demod_completeness_check              fast
% 3.30/0.99  --demod_use_ground                      true
% 3.30/0.99  --sup_to_prop_solver                    passive
% 3.30/0.99  --sup_prop_simpl_new                    true
% 3.30/0.99  --sup_prop_simpl_given                  true
% 3.30/0.99  --sup_fun_splitting                     false
% 3.30/0.99  --sup_smt_interval                      50000
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Simplification Setup
% 3.30/0.99  
% 3.30/0.99  --sup_indices_passive                   []
% 3.30/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_full_bw                           [BwDemod]
% 3.30/0.99  --sup_immed_triv                        [TrivRules]
% 3.30/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_immed_bw_main                     []
% 3.30/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  
% 3.30/0.99  ------ Combination Options
% 3.30/0.99  
% 3.30/0.99  --comb_res_mult                         3
% 3.30/0.99  --comb_sup_mult                         2
% 3.30/0.99  --comb_inst_mult                        10
% 3.30/0.99  
% 3.30/0.99  ------ Debug Options
% 3.30/0.99  
% 3.30/0.99  --dbg_backtrace                         false
% 3.30/0.99  --dbg_dump_prop_clauses                 false
% 3.30/0.99  --dbg_dump_prop_clauses_file            -
% 3.30/0.99  --dbg_out_stat                          false
% 3.30/0.99  ------ Parsing...
% 3.30/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/0.99  ------ Proving...
% 3.30/0.99  ------ Problem Properties 
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  clauses                                 32
% 3.30/0.99  conjectures                             17
% 3.30/0.99  EPR                                     16
% 3.30/0.99  Horn                                    29
% 3.30/0.99  unary                                   17
% 3.30/0.99  binary                                  2
% 3.30/0.99  lits                                    101
% 3.30/0.99  lits eq                                 10
% 3.30/0.99  fd_pure                                 0
% 3.30/0.99  fd_pseudo                               0
% 3.30/0.99  fd_cond                                 0
% 3.30/0.99  fd_pseudo_cond                          0
% 3.30/0.99  AC symbols                              0
% 3.30/0.99  
% 3.30/0.99  ------ Schedule dynamic 5 is on 
% 3.30/0.99  
% 3.30/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  ------ 
% 3.30/0.99  Current options:
% 3.30/0.99  ------ 
% 3.30/0.99  
% 3.30/0.99  ------ Input Options
% 3.30/0.99  
% 3.30/0.99  --out_options                           all
% 3.30/0.99  --tptp_safe_out                         true
% 3.30/0.99  --problem_path                          ""
% 3.30/0.99  --include_path                          ""
% 3.30/0.99  --clausifier                            res/vclausify_rel
% 3.30/0.99  --clausifier_options                    --mode clausify
% 3.30/0.99  --stdin                                 false
% 3.30/0.99  --stats_out                             all
% 3.30/0.99  
% 3.30/0.99  ------ General Options
% 3.30/0.99  
% 3.30/0.99  --fof                                   false
% 3.30/0.99  --time_out_real                         305.
% 3.30/0.99  --time_out_virtual                      -1.
% 3.30/0.99  --symbol_type_check                     false
% 3.30/0.99  --clausify_out                          false
% 3.30/0.99  --sig_cnt_out                           false
% 3.30/0.99  --trig_cnt_out                          false
% 3.30/0.99  --trig_cnt_out_tolerance                1.
% 3.30/0.99  --trig_cnt_out_sk_spl                   false
% 3.30/0.99  --abstr_cl_out                          false
% 3.30/0.99  
% 3.30/0.99  ------ Global Options
% 3.30/0.99  
% 3.30/0.99  --schedule                              default
% 3.30/0.99  --add_important_lit                     false
% 3.30/0.99  --prop_solver_per_cl                    1000
% 3.30/0.99  --min_unsat_core                        false
% 3.30/0.99  --soft_assumptions                      false
% 3.30/0.99  --soft_lemma_size                       3
% 3.30/0.99  --prop_impl_unit_size                   0
% 3.30/0.99  --prop_impl_unit                        []
% 3.30/0.99  --share_sel_clauses                     true
% 3.30/0.99  --reset_solvers                         false
% 3.30/0.99  --bc_imp_inh                            [conj_cone]
% 3.30/0.99  --conj_cone_tolerance                   3.
% 3.30/0.99  --extra_neg_conj                        none
% 3.30/0.99  --large_theory_mode                     true
% 3.30/0.99  --prolific_symb_bound                   200
% 3.30/0.99  --lt_threshold                          2000
% 3.30/0.99  --clause_weak_htbl                      true
% 3.30/0.99  --gc_record_bc_elim                     false
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing Options
% 3.30/0.99  
% 3.30/0.99  --preprocessing_flag                    true
% 3.30/0.99  --time_out_prep_mult                    0.1
% 3.30/0.99  --splitting_mode                        input
% 3.30/0.99  --splitting_grd                         true
% 3.30/0.99  --splitting_cvd                         false
% 3.30/0.99  --splitting_cvd_svl                     false
% 3.30/0.99  --splitting_nvd                         32
% 3.30/0.99  --sub_typing                            true
% 3.30/0.99  --prep_gs_sim                           true
% 3.30/0.99  --prep_unflatten                        true
% 3.30/0.99  --prep_res_sim                          true
% 3.30/0.99  --prep_upred                            true
% 3.30/0.99  --prep_sem_filter                       exhaustive
% 3.30/0.99  --prep_sem_filter_out                   false
% 3.30/0.99  --pred_elim                             true
% 3.30/0.99  --res_sim_input                         true
% 3.30/0.99  --eq_ax_congr_red                       true
% 3.30/0.99  --pure_diseq_elim                       true
% 3.30/0.99  --brand_transform                       false
% 3.30/0.99  --non_eq_to_eq                          false
% 3.30/0.99  --prep_def_merge                        true
% 3.30/0.99  --prep_def_merge_prop_impl              false
% 3.30/0.99  --prep_def_merge_mbd                    true
% 3.30/0.99  --prep_def_merge_tr_red                 false
% 3.30/0.99  --prep_def_merge_tr_cl                  false
% 3.30/0.99  --smt_preprocessing                     true
% 3.30/0.99  --smt_ac_axioms                         fast
% 3.30/0.99  --preprocessed_out                      false
% 3.30/0.99  --preprocessed_stats                    false
% 3.30/0.99  
% 3.30/0.99  ------ Abstraction refinement Options
% 3.30/0.99  
% 3.30/0.99  --abstr_ref                             []
% 3.30/0.99  --abstr_ref_prep                        false
% 3.30/0.99  --abstr_ref_until_sat                   false
% 3.30/0.99  --abstr_ref_sig_restrict                funpre
% 3.30/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.99  --abstr_ref_under                       []
% 3.30/0.99  
% 3.30/0.99  ------ SAT Options
% 3.30/0.99  
% 3.30/0.99  --sat_mode                              false
% 3.30/0.99  --sat_fm_restart_options                ""
% 3.30/0.99  --sat_gr_def                            false
% 3.30/0.99  --sat_epr_types                         true
% 3.30/0.99  --sat_non_cyclic_types                  false
% 3.30/0.99  --sat_finite_models                     false
% 3.30/0.99  --sat_fm_lemmas                         false
% 3.30/0.99  --sat_fm_prep                           false
% 3.30/0.99  --sat_fm_uc_incr                        true
% 3.30/0.99  --sat_out_model                         small
% 3.30/0.99  --sat_out_clauses                       false
% 3.30/0.99  
% 3.30/0.99  ------ QBF Options
% 3.30/0.99  
% 3.30/0.99  --qbf_mode                              false
% 3.30/0.99  --qbf_elim_univ                         false
% 3.30/0.99  --qbf_dom_inst                          none
% 3.30/0.99  --qbf_dom_pre_inst                      false
% 3.30/0.99  --qbf_sk_in                             false
% 3.30/0.99  --qbf_pred_elim                         true
% 3.30/0.99  --qbf_split                             512
% 3.30/0.99  
% 3.30/0.99  ------ BMC1 Options
% 3.30/0.99  
% 3.30/0.99  --bmc1_incremental                      false
% 3.30/0.99  --bmc1_axioms                           reachable_all
% 3.30/0.99  --bmc1_min_bound                        0
% 3.30/0.99  --bmc1_max_bound                        -1
% 3.30/0.99  --bmc1_max_bound_default                -1
% 3.30/0.99  --bmc1_symbol_reachability              true
% 3.30/0.99  --bmc1_property_lemmas                  false
% 3.30/0.99  --bmc1_k_induction                      false
% 3.30/0.99  --bmc1_non_equiv_states                 false
% 3.30/0.99  --bmc1_deadlock                         false
% 3.30/0.99  --bmc1_ucm                              false
% 3.30/0.99  --bmc1_add_unsat_core                   none
% 3.30/0.99  --bmc1_unsat_core_children              false
% 3.30/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.99  --bmc1_out_stat                         full
% 3.30/0.99  --bmc1_ground_init                      false
% 3.30/0.99  --bmc1_pre_inst_next_state              false
% 3.30/0.99  --bmc1_pre_inst_state                   false
% 3.30/0.99  --bmc1_pre_inst_reach_state             false
% 3.30/0.99  --bmc1_out_unsat_core                   false
% 3.30/0.99  --bmc1_aig_witness_out                  false
% 3.30/0.99  --bmc1_verbose                          false
% 3.30/0.99  --bmc1_dump_clauses_tptp                false
% 3.30/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.99  --bmc1_dump_file                        -
% 3.30/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.99  --bmc1_ucm_extend_mode                  1
% 3.30/0.99  --bmc1_ucm_init_mode                    2
% 3.30/0.99  --bmc1_ucm_cone_mode                    none
% 3.30/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.99  --bmc1_ucm_relax_model                  4
% 3.30/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.99  --bmc1_ucm_layered_model                none
% 3.30/0.99  --bmc1_ucm_max_lemma_size               10
% 3.30/0.99  
% 3.30/0.99  ------ AIG Options
% 3.30/0.99  
% 3.30/0.99  --aig_mode                              false
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation Options
% 3.30/0.99  
% 3.30/0.99  --instantiation_flag                    true
% 3.30/0.99  --inst_sos_flag                         false
% 3.30/0.99  --inst_sos_phase                        true
% 3.30/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel_side                     none
% 3.30/0.99  --inst_solver_per_active                1400
% 3.30/0.99  --inst_solver_calls_frac                1.
% 3.30/0.99  --inst_passive_queue_type               priority_queues
% 3.30/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.99  --inst_passive_queues_freq              [25;2]
% 3.30/0.99  --inst_dismatching                      true
% 3.30/0.99  --inst_eager_unprocessed_to_passive     true
% 3.30/0.99  --inst_prop_sim_given                   true
% 3.30/0.99  --inst_prop_sim_new                     false
% 3.30/0.99  --inst_subs_new                         false
% 3.30/0.99  --inst_eq_res_simp                      false
% 3.30/0.99  --inst_subs_given                       false
% 3.30/0.99  --inst_orphan_elimination               true
% 3.30/0.99  --inst_learning_loop_flag               true
% 3.30/0.99  --inst_learning_start                   3000
% 3.30/0.99  --inst_learning_factor                  2
% 3.30/0.99  --inst_start_prop_sim_after_learn       3
% 3.30/0.99  --inst_sel_renew                        solver
% 3.30/0.99  --inst_lit_activity_flag                true
% 3.30/0.99  --inst_restr_to_given                   false
% 3.30/0.99  --inst_activity_threshold               500
% 3.30/0.99  --inst_out_proof                        true
% 3.30/0.99  
% 3.30/0.99  ------ Resolution Options
% 3.30/0.99  
% 3.30/0.99  --resolution_flag                       false
% 3.30/0.99  --res_lit_sel                           adaptive
% 3.30/0.99  --res_lit_sel_side                      none
% 3.30/0.99  --res_ordering                          kbo
% 3.30/0.99  --res_to_prop_solver                    active
% 3.30/0.99  --res_prop_simpl_new                    false
% 3.30/0.99  --res_prop_simpl_given                  true
% 3.30/0.99  --res_passive_queue_type                priority_queues
% 3.30/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.99  --res_passive_queues_freq               [15;5]
% 3.30/0.99  --res_forward_subs                      full
% 3.30/0.99  --res_backward_subs                     full
% 3.30/0.99  --res_forward_subs_resolution           true
% 3.30/0.99  --res_backward_subs_resolution          true
% 3.30/0.99  --res_orphan_elimination                true
% 3.30/0.99  --res_time_limit                        2.
% 3.30/0.99  --res_out_proof                         true
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Options
% 3.30/0.99  
% 3.30/0.99  --superposition_flag                    true
% 3.30/0.99  --sup_passive_queue_type                priority_queues
% 3.30/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.99  --demod_completeness_check              fast
% 3.30/0.99  --demod_use_ground                      true
% 3.30/0.99  --sup_to_prop_solver                    passive
% 3.30/0.99  --sup_prop_simpl_new                    true
% 3.30/0.99  --sup_prop_simpl_given                  true
% 3.30/0.99  --sup_fun_splitting                     false
% 3.30/0.99  --sup_smt_interval                      50000
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Simplification Setup
% 3.30/0.99  
% 3.30/0.99  --sup_indices_passive                   []
% 3.30/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_full_bw                           [BwDemod]
% 3.30/0.99  --sup_immed_triv                        [TrivRules]
% 3.30/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_immed_bw_main                     []
% 3.30/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  
% 3.30/0.99  ------ Combination Options
% 3.30/0.99  
% 3.30/0.99  --comb_res_mult                         3
% 3.30/0.99  --comb_sup_mult                         2
% 3.30/0.99  --comb_inst_mult                        10
% 3.30/0.99  
% 3.30/0.99  ------ Debug Options
% 3.30/0.99  
% 3.30/0.99  --dbg_backtrace                         false
% 3.30/0.99  --dbg_dump_prop_clauses                 false
% 3.30/0.99  --dbg_dump_prop_clauses_file            -
% 3.30/0.99  --dbg_out_stat                          false
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  ------ Proving...
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS status Theorem for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  fof(f16,conjecture,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f17,negated_conjecture,(
% 3.30/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.30/0.99    inference(negated_conjecture,[],[f16])).
% 3.30/0.99  
% 3.30/0.99  fof(f42,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f17])).
% 3.30/0.99  
% 3.30/0.99  fof(f43,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f42])).
% 3.30/0.99  
% 3.30/0.99  fof(f53,plain,(
% 3.30/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f52,plain,(
% 3.30/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f51,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f50,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f49,plain,(
% 3.30/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f48,plain,(
% 3.30/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f47,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f54,plain,(
% 3.30/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f53,f52,f51,f50,f49,f48,f47])).
% 3.30/0.99  
% 3.30/0.99  fof(f81,plain,(
% 3.30/0.99    m1_pre_topc(sK2,sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f5,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f24,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f5])).
% 3.30/0.99  
% 3.30/0.99  fof(f59,plain,(
% 3.30/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f24])).
% 3.30/0.99  
% 3.30/0.99  fof(f76,plain,(
% 3.30/0.99    l1_pre_topc(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f4,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f23,plain,(
% 3.30/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f4])).
% 3.30/0.99  
% 3.30/0.99  fof(f58,plain,(
% 3.30/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f23])).
% 3.30/0.99  
% 3.30/0.99  fof(f3,axiom,(
% 3.30/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f22,plain,(
% 3.30/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f3])).
% 3.30/0.99  
% 3.30/0.99  fof(f57,plain,(
% 3.30/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f9,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f30,plain,(
% 3.30/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f9])).
% 3.30/0.99  
% 3.30/0.99  fof(f31,plain,(
% 3.30/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f30])).
% 3.30/0.99  
% 3.30/0.99  fof(f64,plain,(
% 3.30/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f31])).
% 3.30/0.99  
% 3.30/0.99  fof(f75,plain,(
% 3.30/0.99    v2_pre_topc(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f2,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f20,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f2])).
% 3.30/0.99  
% 3.30/0.99  fof(f21,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f20])).
% 3.30/0.99  
% 3.30/0.99  fof(f56,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f21])).
% 3.30/0.99  
% 3.30/0.99  fof(f12,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f36,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f12])).
% 3.30/0.99  
% 3.30/0.99  fof(f69,plain,(
% 3.30/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f36])).
% 3.30/0.99  
% 3.30/0.99  fof(f10,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f32,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f10])).
% 3.30/0.99  
% 3.30/0.99  fof(f33,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f32])).
% 3.30/0.99  
% 3.30/0.99  fof(f65,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f33])).
% 3.30/0.99  
% 3.30/0.99  fof(f93,plain,(
% 3.30/0.99    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(equality_resolution,[],[f65])).
% 3.30/0.99  
% 3.30/0.99  fof(f8,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f29,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f8])).
% 3.30/0.99  
% 3.30/0.99  fof(f63,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f29])).
% 3.30/0.99  
% 3.30/0.99  fof(f91,plain,(
% 3.30/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f90,plain,(
% 3.30/0.99    sK5 = sK6),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f11,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f34,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f11])).
% 3.30/0.99  
% 3.30/0.99  fof(f35,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f34])).
% 3.30/0.99  
% 3.30/0.99  fof(f44,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/0.99    inference(nnf_transformation,[],[f35])).
% 3.30/0.99  
% 3.30/0.99  fof(f45,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f67,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f45])).
% 3.30/0.99  
% 3.30/0.99  fof(f95,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/0.99    inference(equality_resolution,[],[f67])).
% 3.30/0.99  
% 3.30/0.99  fof(f15,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f40,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f15])).
% 3.30/0.99  
% 3.30/0.99  fof(f41,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f40])).
% 3.30/0.99  
% 3.30/0.99  fof(f46,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(nnf_transformation,[],[f41])).
% 3.30/0.99  
% 3.30/0.99  fof(f73,plain,(
% 3.30/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f46])).
% 3.30/0.99  
% 3.30/0.99  fof(f97,plain,(
% 3.30/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(equality_resolution,[],[f73])).
% 3.30/0.99  
% 3.30/0.99  fof(f85,plain,(
% 3.30/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f84,plain,(
% 3.30/0.99    v1_funct_1(sK4)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f14,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f38,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f14])).
% 3.30/0.99  
% 3.30/0.99  fof(f39,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f38])).
% 3.30/0.99  
% 3.30/0.99  fof(f71,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f39])).
% 3.30/0.99  
% 3.30/0.99  fof(f77,plain,(
% 3.30/0.99    ~v2_struct_0(sK1)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f78,plain,(
% 3.30/0.99    v2_pre_topc(sK1)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f79,plain,(
% 3.30/0.99    l1_pre_topc(sK1)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f82,plain,(
% 3.30/0.99    ~v2_struct_0(sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f86,plain,(
% 3.30/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f74,plain,(
% 3.30/0.99    ~v2_struct_0(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f80,plain,(
% 3.30/0.99    ~v2_struct_0(sK2)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f83,plain,(
% 3.30/0.99    m1_pre_topc(sK3,sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f88,plain,(
% 3.30/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f92,plain,(
% 3.30/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f89,plain,(
% 3.30/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f13,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f37,plain,(
% 3.30/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f13])).
% 3.30/0.99  
% 3.30/0.99  fof(f70,plain,(
% 3.30/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f37])).
% 3.30/0.99  
% 3.30/0.99  fof(f1,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f18,plain,(
% 3.30/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f1])).
% 3.30/0.99  
% 3.30/0.99  fof(f19,plain,(
% 3.30/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f18])).
% 3.30/0.99  
% 3.30/0.99  fof(f55,plain,(
% 3.30/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f19])).
% 3.30/0.99  
% 3.30/0.99  fof(f87,plain,(
% 3.30/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.30/0.99    inference(cnf_transformation,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f6,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f25,plain,(
% 3.30/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f6])).
% 3.30/0.99  
% 3.30/0.99  fof(f26,plain,(
% 3.30/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f25])).
% 3.30/0.99  
% 3.30/0.99  fof(f61,plain,(
% 3.30/0.99    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f26])).
% 3.30/0.99  
% 3.30/0.99  fof(f7,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f27,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f7])).
% 3.30/0.99  
% 3.30/0.99  fof(f28,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f27])).
% 3.30/0.99  
% 3.30/0.99  fof(f62,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f28])).
% 3.30/0.99  
% 3.30/0.99  cnf(c_30,negated_conjecture,
% 3.30/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_922,negated_conjecture,
% 3.30/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1535,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_940,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.30/0.99      | ~ l1_pre_topc(X1_54)
% 3.30/0.99      | l1_pre_topc(X0_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1519,plain,
% 3.30/0.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2448,plain,
% 3.30/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_1535,c_1519]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_35,negated_conjecture,
% 3.30/0.99      ( l1_pre_topc(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_40,plain,
% 3.30/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2653,plain,
% 3.30/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2448,c_40]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3,plain,
% 3.30/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2,plain,
% 3.30/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_383,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.30/0.99      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_913,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0_54) | k2_struct_0(X0_54) = u1_struct_0(X0_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_383]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1544,plain,
% 3.30/0.99      ( k2_struct_0(X0_54) = u1_struct_0(X0_54)
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3081,plain,
% 3.30/0.99      ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2653,c_1544]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_9,plain,
% 3.30/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.30/0.99      | ~ v2_pre_topc(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_936,plain,
% 3.30/0.99      ( v3_pre_topc(k2_struct_0(X0_54),X0_54)
% 3.30/0.99      | ~ v2_pre_topc(X0_54)
% 3.30/0.99      | ~ l1_pre_topc(X0_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1523,plain,
% 3.30/0.99      ( v3_pre_topc(k2_struct_0(X0_54),X0_54) = iProver_top
% 3.30/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3375,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top
% 3.30/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_3081,c_1523]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_36,negated_conjecture,
% 3.30/0.99      ( v2_pre_topc(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_39,plain,
% 3.30/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_pre_topc(X0)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_941,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.30/0.99      | ~ v2_pre_topc(X1_54)
% 3.30/0.99      | v2_pre_topc(X0_54)
% 3.30/0.99      | ~ l1_pre_topc(X1_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1518,plain,
% 3.30/0.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.30/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | v2_pre_topc(X0_54) = iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_941]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2356,plain,
% 3.30/0.99      ( v2_pre_topc(sK0) != iProver_top
% 3.30/0.99      | v2_pre_topc(sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_1535,c_1518]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4776,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3375,c_39,c_40,c_2356,c_2448]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_14,plain,
% 3.30/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_934,plain,
% 3.30/0.99      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
% 3.30/0.99      | ~ m1_pre_topc(X0_54,X1_54)
% 3.30/0.99      | ~ l1_pre_topc(X1_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1525,plain,
% 3.30/0.99      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10,plain,
% 3.30/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.30/0.99      | v3_pre_topc(X0,X2)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | ~ m1_pre_topc(X2,X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_935,plain,
% 3.30/0.99      ( ~ v3_pre_topc(X0_55,X0_54)
% 3.30/0.99      | v3_pre_topc(X0_55,X1_54)
% 3.30/0.99      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
% 3.30/0.99      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
% 3.30/0.99      | ~ m1_pre_topc(X1_54,X0_54)
% 3.30/0.99      | ~ l1_pre_topc(X0_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1524,plain,
% 3.30/0.99      ( v3_pre_topc(X0_55,X0_54) != iProver_top
% 3.30/0.99      | v3_pre_topc(X0_55,X1_54) = iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_8,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.30/0.99      | ~ m1_pre_topc(X1,X2)
% 3.30/0.99      | ~ l1_pre_topc(X2) ),
% 3.30/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_937,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
% 3.30/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
% 3.30/0.99      | ~ m1_pre_topc(X0_54,X1_54)
% 3.30/0.99      | ~ l1_pre_topc(X1_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1522,plain,
% 3.30/0.99      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1659,plain,
% 3.30/0.99      ( v3_pre_topc(X0_55,X0_54) != iProver_top
% 3.30/0.99      | v3_pre_topc(X0_55,X1_54) = iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(forward_subsumption_resolution,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_1524,c_1522]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4681,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(X0_54),X1_54) != iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X0_54),X2_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_1525,c_1659]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6136,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(X0_54),X1_54) != iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X0_54),X2_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(forward_subsumption_resolution,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_4681,c_1519]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6141,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(sK2),X0_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_4776,c_6136]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_8721,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,X0_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(sK2),X0_54) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_6141,c_40,c_2448]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_8722,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(sK2),X0_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_8721]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_20,negated_conjecture,
% 3.30/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.30/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_930,negated_conjecture,
% 3.30/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1529,plain,
% 3.30/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_21,negated_conjecture,
% 3.30/0.99      ( sK5 = sK6 ),
% 3.30/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_929,negated_conjecture,
% 3.30/0.99      ( sK5 = sK6 ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1588,plain,
% 3.30/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.30/0.99      inference(light_normalisation,[status(thm)],[c_1529,c_929]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_12,plain,
% 3.30/0.99      ( v1_tsep_1(X0,X1)
% 3.30/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_200,plain,
% 3.30/0.99      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/0.99      | v1_tsep_1(X0,X1)
% 3.30/0.99      | ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_12,c_14]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_201,plain,
% 3.30/0.99      ( v1_tsep_1(X0,X1)
% 3.30/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.30/0.99      | ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_200]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_17,plain,
% 3.30/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.30/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.30/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.30/0.99      | ~ v1_tsep_1(X4,X0)
% 3.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_pre_topc(X4,X5)
% 3.30/0.99      | ~ m1_pre_topc(X0,X5)
% 3.30/0.99      | ~ m1_pre_topc(X4,X0)
% 3.30/0.99      | ~ v1_funct_1(X2)
% 3.30/0.99      | v2_struct_0(X5)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X4)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X5)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X5)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_26,negated_conjecture,
% 3.30/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_488,plain,
% 3.30/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.30/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.30/0.99      | ~ v1_tsep_1(X4,X0)
% 3.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.30/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_pre_topc(X4,X5)
% 3.30/0.99      | ~ m1_pre_topc(X0,X5)
% 3.30/0.99      | ~ m1_pre_topc(X4,X0)
% 3.30/0.99      | ~ v1_funct_1(X2)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X5)
% 3.30/0.99      | v2_struct_0(X4)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X5)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X5)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.30/0.99      | sK4 != X2 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_489,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ v1_tsep_1(X0,X3)
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_pre_topc(X0,X2)
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | ~ v1_funct_1(sK4)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_488]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_27,negated_conjecture,
% 3.30/0.99      ( v1_funct_1(sK4) ),
% 3.30/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_493,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | ~ m1_pre_topc(X0,X2)
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ v1_tsep_1(X0,X3)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_489,c_27]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_494,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ v1_tsep_1(X0,X3)
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | ~ m1_pre_topc(X0,X2)
% 3.30/0.99      | ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_493]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_16,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ m1_pre_topc(X2,X0)
% 3.30/0.99      | m1_pre_topc(X2,X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_537,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ v1_tsep_1(X0,X3)
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(forward_subsumption_resolution,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_494,c_16]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_560,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ v3_pre_topc(u1_struct_0(X5),X6)
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_pre_topc(X5,X6)
% 3.30/0.99      | ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ v2_pre_topc(X6)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X6)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | X0 != X5
% 3.30/0.99      | X3 != X6
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_201,c_537]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_561,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ v2_pre_topc(X3)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X3)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_560]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_605,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.30/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.30/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.30/0.99      | ~ m1_pre_topc(X3,X2)
% 3.30/0.99      | ~ m1_pre_topc(X0,X3)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X3)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(forward_subsumption_resolution,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_561,c_4,c_1]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_912,plain,
% 3.30/0.99      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
% 3.30/0.99      | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
% 3.30/0.99      | ~ v3_pre_topc(u1_struct_0(X0_54),X3_54)
% 3.30/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 3.30/0.99      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 3.30/0.99      | ~ m1_pre_topc(X3_54,X2_54)
% 3.30/0.99      | ~ m1_pre_topc(X0_54,X3_54)
% 3.30/0.99      | v2_struct_0(X0_54)
% 3.30/0.99      | v2_struct_0(X1_54)
% 3.30/0.99      | v2_struct_0(X3_54)
% 3.30/0.99      | v2_struct_0(X2_54)
% 3.30/0.99      | ~ v2_pre_topc(X1_54)
% 3.30/0.99      | ~ v2_pre_topc(X2_54)
% 3.30/0.99      | ~ l1_pre_topc(X1_54)
% 3.30/0.99      | ~ l1_pre_topc(X2_54)
% 3.30/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_605]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1545,plain,
% 3.30/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 3.30/0.99      | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X2_54),X1_54) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.30/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | v2_pre_topc(X3_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X3_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2346,plain,
% 3.30/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 3.30/0.99      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.30/0.99      | v2_struct_0(sK1) = iProver_top
% 3.30/0.99      | v2_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.30/0.99      inference(equality_resolution,[status(thm)],[c_1545]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_34,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_41,plain,
% 3.30/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_33,negated_conjecture,
% 3.30/0.99      ( v2_pre_topc(sK1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_42,plain,
% 3.30/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_32,negated_conjecture,
% 3.30/0.99      ( l1_pre_topc(sK1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_43,plain,
% 3.30/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5392,plain,
% 3.30/0.99      ( l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 3.30/0.99      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 3.30/0.99      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 3.30/0.99      | v2_pre_topc(X2_54) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2346,c_41,c_42,c_43]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5393,plain,
% 3.30/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 3.30/0.99      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.30/0.99      | v2_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_5392]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5410,plain,
% 3.30/0.99      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(equality_resolution,[status(thm)],[c_5393]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_29,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_46,plain,
% 3.30/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_25,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_50,plain,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10435,plain,
% 3.30/0.99      ( v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.30/0.99      | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 3.30/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5410,c_46,c_50]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10436,plain,
% 3.30/0.99      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 3.30/0.99      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.30/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.30/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_10435]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10452,plain,
% 3.30/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.30/0.99      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.30/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.30/0.99      | v2_struct_0(sK0) = iProver_top
% 3.30/0.99      | v2_struct_0(sK2) = iProver_top
% 3.30/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_1588,c_10436]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_37,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_38,plain,
% 3.30/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_31,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK2) ),
% 3.30/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_44,plain,
% 3.30/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_28,negated_conjecture,
% 3.30/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_47,plain,
% 3.30/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_23,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_51,plain,
% 3.30/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_19,negated_conjecture,
% 3.30/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.30/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_54,plain,
% 3.30/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_22,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_928,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1530,plain,
% 3.30/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1569,plain,
% 3.30/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.30/0.99      inference(light_normalisation,[status(thm)],[c_1530,c_929]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_15,plain,
% 3.30/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_933,plain,
% 3.30/0.99      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1526,plain,
% 3.30/0.99      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_924,negated_conjecture,
% 3.30/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1533,plain,
% 3.30/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2447,plain,
% 3.30/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_1533,c_1519]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2598,plain,
% 3.30/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2447,c_40]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_0,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0)
% 3.30/0.99      | ~ v1_pre_topc(X0)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.30/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_942,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0_54)
% 3.30/0.99      | ~ v1_pre_topc(X0_54)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = X0_54 ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1517,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = X0_54
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | v1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2603,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 3.30/0.99      | v1_pre_topc(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2598,c_1517]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_24,negated_conjecture,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.30/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_926,negated_conjecture,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5,plain,
% 3.30/0.99      ( v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_939,plain,
% 3.30/0.99      ( v2_struct_0(X0_54)
% 3.30/0.99      | ~ l1_pre_topc(X0_54)
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1520,plain,
% 3.30/0.99      ( v2_struct_0(X0_54) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2514,plain,
% 3.30/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.30/0.99      | v1_pre_topc(sK3) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_926,c_1520]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2816,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2603,c_40,c_44,c_2448,c_2514]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | m1_pre_topc(X2,X3)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X3)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_210,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X3)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | m1_pre_topc(X2,X3)
% 3.30/0.99      | ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7,c_4]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_211,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | m1_pre_topc(X2,X3)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X3)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_914,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.30/0.99      | m1_pre_topc(X2_54,X3_54)
% 3.30/0.99      | ~ l1_pre_topc(X1_54)
% 3.30/0.99      | ~ l1_pre_topc(X2_54)
% 3.30/0.99      | ~ l1_pre_topc(X3_54)
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X3_54),u1_pre_topc(X3_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_211]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1543,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != g1_pre_topc(u1_struct_0(X3_54),u1_pre_topc(X3_54))
% 3.30/0.99      | m1_pre_topc(X3_54,X1_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X2_54,X0_54) = iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_914]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3467,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
% 3.30/0.99      | m1_pre_topc(X1_54,X2_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_926,c_1543]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3816,plain,
% 3.30/0.99      ( l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,X2_54) = iProver_top
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3467,c_40,c_2448]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3817,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
% 3.30/0.99      | m1_pre_topc(X1_54,X2_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_3816]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3826,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) != sK3
% 3.30/0.99      | m1_pre_topc(X0_54,X1_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_926,c_3817]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3905,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_926,c_3826]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3992,plain,
% 3.30/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) = iProver_top
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3905,c_40,c_2448]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3993,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_3992]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4003,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2816,c_3993]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4131,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_4003,c_40,c_2447]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4132,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_4131]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4137,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_1526,c_4132]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10455,plain,
% 3.30/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_10452,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1569,
% 3.30/0.99                 c_2448,c_4137]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10461,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_8722,c_10455]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3465,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_926,c_1543]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3628,plain,
% 3.30/0.99      ( l1_pre_topc(X2_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,sK2) = iProver_top
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3465,c_40,c_2448]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3629,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54))
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X2_54),u1_pre_topc(X2_54)) != sK3
% 3.30/0.99      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(X1_54,sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X2_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_3628]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3640,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X1_54),u1_pre_topc(X1_54)) != sK3
% 3.30/0.99      | m1_pre_topc(X0_54,sK2) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_926,c_3629]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3717,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2816,c_3640]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4265,plain,
% 3.30/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,sK2) = iProver_top
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) != iProver_top
% 3.30/0.99      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3717,c_40,c_2447]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4266,plain,
% 3.30/0.99      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) != sK3
% 3.30/0.99      | m1_pre_topc(sK2,X0_54) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0_54) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_4265]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4276,plain,
% 3.30/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK3,sK2) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2816,c_4266]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(contradiction,plain,
% 3.30/0.99      ( $false ),
% 3.30/0.99      inference(minisat,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_10461,c_4276,c_4137,c_2448,c_2447,c_40]) ).
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  ------                               Statistics
% 3.30/0.99  
% 3.30/0.99  ------ General
% 3.30/0.99  
% 3.30/0.99  abstr_ref_over_cycles:                  0
% 3.30/0.99  abstr_ref_under_cycles:                 0
% 3.30/0.99  gc_basic_clause_elim:                   0
% 3.30/0.99  forced_gc_time:                         0
% 3.30/0.99  parsing_time:                           0.01
% 3.30/0.99  unif_index_cands_time:                  0.
% 3.30/0.99  unif_index_add_time:                    0.
% 3.30/0.99  orderings_time:                         0.
% 3.30/0.99  out_proof_time:                         0.015
% 3.30/0.99  total_time:                             0.285
% 3.30/0.99  num_of_symbols:                         60
% 3.30/0.99  num_of_terms:                           5121
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing
% 3.30/0.99  
% 3.30/0.99  num_of_splits:                          0
% 3.30/0.99  num_of_split_atoms:                     0
% 3.30/0.99  num_of_reused_defs:                     0
% 3.30/0.99  num_eq_ax_congr_red:                    9
% 3.30/0.99  num_of_sem_filtered_clauses:            1
% 3.30/0.99  num_of_subtypes:                        3
% 3.30/0.99  monotx_restored_types:                  0
% 3.30/0.99  sat_num_of_epr_types:                   0
% 3.30/0.99  sat_num_of_non_cyclic_types:            0
% 3.30/0.99  sat_guarded_non_collapsed_types:        1
% 3.30/0.99  num_pure_diseq_elim:                    0
% 3.30/0.99  simp_replaced_by:                       0
% 3.30/0.99  res_preprocessed:                       172
% 3.30/0.99  prep_upred:                             0
% 3.30/0.99  prep_unflattend:                        8
% 3.30/0.99  smt_new_axioms:                         0
% 3.30/0.99  pred_elim_cands:                        8
% 3.30/0.99  pred_elim:                              4
% 3.30/0.99  pred_elim_cl:                           5
% 3.30/0.99  pred_elim_cycles:                       7
% 3.30/0.99  merged_defs:                            0
% 3.30/0.99  merged_defs_ncl:                        0
% 3.30/0.99  bin_hyper_res:                          0
% 3.30/0.99  prep_cycles:                            4
% 3.30/0.99  pred_elim_time:                         0.008
% 3.30/0.99  splitting_time:                         0.
% 3.30/0.99  sem_filter_time:                        0.
% 3.30/0.99  monotx_time:                            0.
% 3.30/0.99  subtype_inf_time:                       0.
% 3.30/0.99  
% 3.30/0.99  ------ Problem properties
% 3.30/0.99  
% 3.30/0.99  clauses:                                32
% 3.30/0.99  conjectures:                            17
% 3.30/0.99  epr:                                    16
% 3.30/0.99  horn:                                   29
% 3.30/0.99  ground:                                 17
% 3.30/0.99  unary:                                  17
% 3.30/0.99  binary:                                 2
% 3.30/0.99  lits:                                   101
% 3.30/0.99  lits_eq:                                10
% 3.30/0.99  fd_pure:                                0
% 3.30/0.99  fd_pseudo:                              0
% 3.30/0.99  fd_cond:                                0
% 3.30/0.99  fd_pseudo_cond:                         0
% 3.30/0.99  ac_symbols:                             0
% 3.30/0.99  
% 3.30/0.99  ------ Propositional Solver
% 3.30/0.99  
% 3.30/0.99  prop_solver_calls:                      30
% 3.30/0.99  prop_fast_solver_calls:                 2003
% 3.30/0.99  smt_solver_calls:                       0
% 3.30/0.99  smt_fast_solver_calls:                  0
% 3.30/0.99  prop_num_of_clauses:                    3157
% 3.30/0.99  prop_preprocess_simplified:             8105
% 3.30/0.99  prop_fo_subsumed:                       113
% 3.30/0.99  prop_solver_time:                       0.
% 3.30/0.99  smt_solver_time:                        0.
% 3.30/0.99  smt_fast_solver_time:                   0.
% 3.30/0.99  prop_fast_solver_time:                  0.
% 3.30/0.99  prop_unsat_core_time:                   0.
% 3.30/0.99  
% 3.30/0.99  ------ QBF
% 3.30/0.99  
% 3.30/0.99  qbf_q_res:                              0
% 3.30/0.99  qbf_num_tautologies:                    0
% 3.30/0.99  qbf_prep_cycles:                        0
% 3.30/0.99  
% 3.30/0.99  ------ BMC1
% 3.30/0.99  
% 3.30/0.99  bmc1_current_bound:                     -1
% 3.30/0.99  bmc1_last_solved_bound:                 -1
% 3.30/0.99  bmc1_unsat_core_size:                   -1
% 3.30/0.99  bmc1_unsat_core_parents_size:           -1
% 3.30/0.99  bmc1_merge_next_fun:                    0
% 3.30/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation
% 3.30/0.99  
% 3.30/0.99  inst_num_of_clauses:                    1042
% 3.30/0.99  inst_num_in_passive:                    257
% 3.30/0.99  inst_num_in_active:                     601
% 3.30/0.99  inst_num_in_unprocessed:                185
% 3.30/0.99  inst_num_of_loops:                      630
% 3.30/0.99  inst_num_of_learning_restarts:          0
% 3.30/0.99  inst_num_moves_active_passive:          23
% 3.30/0.99  inst_lit_activity:                      0
% 3.30/0.99  inst_lit_activity_moves:                0
% 3.30/0.99  inst_num_tautologies:                   0
% 3.30/0.99  inst_num_prop_implied:                  0
% 3.30/0.99  inst_num_existing_simplified:           0
% 3.30/0.99  inst_num_eq_res_simplified:             0
% 3.30/0.99  inst_num_child_elim:                    0
% 3.30/0.99  inst_num_of_dismatching_blockings:      699
% 3.30/0.99  inst_num_of_non_proper_insts:           1569
% 3.30/0.99  inst_num_of_duplicates:                 0
% 3.30/0.99  inst_inst_num_from_inst_to_res:         0
% 3.30/0.99  inst_dismatching_checking_time:         0.
% 3.30/0.99  
% 3.30/0.99  ------ Resolution
% 3.30/0.99  
% 3.30/0.99  res_num_of_clauses:                     0
% 3.30/0.99  res_num_in_passive:                     0
% 3.30/0.99  res_num_in_active:                      0
% 3.30/0.99  res_num_of_loops:                       176
% 3.30/0.99  res_forward_subset_subsumed:            157
% 3.30/0.99  res_backward_subset_subsumed:           6
% 3.30/0.99  res_forward_subsumed:                   0
% 3.30/0.99  res_backward_subsumed:                  0
% 3.30/0.99  res_forward_subsumption_resolution:     6
% 3.30/0.99  res_backward_subsumption_resolution:    0
% 3.30/0.99  res_clause_to_clause_subsumption:       1342
% 3.30/0.99  res_orphan_elimination:                 0
% 3.30/0.99  res_tautology_del:                      293
% 3.30/0.99  res_num_eq_res_simplified:              0
% 3.30/0.99  res_num_sel_changes:                    0
% 3.30/0.99  res_moves_from_active_to_pass:          0
% 3.30/0.99  
% 3.30/0.99  ------ Superposition
% 3.30/0.99  
% 3.30/0.99  sup_time_total:                         0.
% 3.30/0.99  sup_time_generating:                    0.
% 3.30/0.99  sup_time_sim_full:                      0.
% 3.30/0.99  sup_time_sim_immed:                     0.
% 3.30/0.99  
% 3.30/0.99  sup_num_of_clauses:                     161
% 3.30/0.99  sup_num_in_active:                      126
% 3.30/0.99  sup_num_in_passive:                     35
% 3.30/0.99  sup_num_of_loops:                       125
% 3.30/0.99  sup_fw_superposition:                   151
% 3.30/0.99  sup_bw_superposition:                   124
% 3.30/0.99  sup_immediate_simplified:               101
% 3.30/0.99  sup_given_eliminated:                   0
% 3.30/0.99  comparisons_done:                       0
% 3.30/0.99  comparisons_avoided:                    0
% 3.30/0.99  
% 3.30/0.99  ------ Simplifications
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  sim_fw_subset_subsumed:                 50
% 3.30/0.99  sim_bw_subset_subsumed:                 9
% 3.30/0.99  sim_fw_subsumed:                        51
% 3.30/0.99  sim_bw_subsumed:                        0
% 3.30/0.99  sim_fw_subsumption_res:                 8
% 3.30/0.99  sim_bw_subsumption_res:                 0
% 3.30/0.99  sim_tautology_del:                      18
% 3.30/0.99  sim_eq_tautology_del:                   0
% 3.30/0.99  sim_eq_res_simp:                        0
% 3.30/0.99  sim_fw_demodulated:                     0
% 3.30/0.99  sim_bw_demodulated:                     0
% 3.30/0.99  sim_light_normalised:                   3
% 3.30/0.99  sim_joinable_taut:                      0
% 3.30/0.99  sim_joinable_simp:                      0
% 3.30/0.99  sim_ac_normalised:                      0
% 3.30/0.99  sim_smt_subsumption:                    0
% 3.30/0.99  
%------------------------------------------------------------------------------
