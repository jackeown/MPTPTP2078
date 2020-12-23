%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:37 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  201 (1250 expanded)
%              Number of clauses        :  118 ( 315 expanded)
%              Number of leaves         :   23 ( 518 expanded)
%              Depth                    :   27
%              Number of atoms          : 1091 (15752 expanded)
%              Number of equality atoms :  339 (2472 expanded)
%              Maximal formula depth    :   32 (   6 average)
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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f47,f46,f45,f44,f43,f42,f41])).

fof(f83,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(nnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(equality_resolution,[],[f65])).

fof(f77,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1948,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2004,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1948,c_19])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1944,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1954,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3033,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1944,c_1954])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3352,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_38])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_386,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_1932,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_3357,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3352,c_1932])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_483,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r2_hidden(X3,X6)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_484,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_488,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_hidden(X4,X5)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(X5,X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_25])).

cnf(c_489,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(renaming,[status(thm)],[c_488])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_538,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_489,c_14])).

cnf(c_642,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | k2_struct_0(X6) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_538])).

cnf(c_643,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_691,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
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
    inference(forward_subsumption_resolution,[status(thm)],[c_643,c_3,c_6])).

cnf(c_1931,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
    | r1_tarski(k2_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_2712,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1931])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5130,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2712,c_39,c_40,c_41])).

cnf(c_5131,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5130])).

cnf(c_1940,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2828,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1940,c_1932])).

cnf(c_5134,plain,
    ( u1_struct_0(X0) != k2_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5131,c_2828,c_3357])).

cnf(c_5155,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3357,c_5134])).

cnf(c_5239,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5155,c_3357])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1945,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3157,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2828,c_1945])).

cnf(c_4085,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3357,c_3157])).

cnf(c_12490,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5239,c_44,c_4085])).

cnf(c_12491,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12490])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1957,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1957,c_0])).

cnf(c_12509,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12491,c_1989])).

cnf(c_12513,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_12509])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1942,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3034,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_1954])).

cnf(c_3359,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3034,c_38])).

cnf(c_3364,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3359,c_1932])).

cnf(c_12526,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12513,c_3364])).

cnf(c_13,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1951,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4096,plain,
    ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3357,c_1951])).

cnf(c_5909,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_4096])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1952,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_182,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_6])).

cnf(c_183,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_1934,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_4410,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3364,c_1934])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4233,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3364,c_22])).

cnf(c_4448,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4410,c_4233])).

cnf(c_4596,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4448,c_38,c_3034])).

cnf(c_4597,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4596])).

cnf(c_4604,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_4597])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1947,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1984,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1947,c_19])).

cnf(c_4232,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3364,c_1984])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1946,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4086,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3357,c_1946])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1956,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3049,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1956])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2233,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2234,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_372,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_2315,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_2316,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_3455,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3049,c_38,c_44,c_49,c_2234,c_2316,c_3033])).

cnf(c_4084,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3357,c_3455])).

cnf(c_8,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1953,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3725,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1953])).

cnf(c_3863,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3725,c_38,c_3034])).

cnf(c_3864,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3863])).

cnf(c_3871,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_3864])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_52,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12526,c_5909,c_4604,c_4232,c_4086,c_4084,c_3871,c_3034,c_3033,c_52,c_45,c_42,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.77/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.04  
% 2.77/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/1.04  
% 2.77/1.04  ------  iProver source info
% 2.77/1.04  
% 2.77/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.77/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/1.04  git: non_committed_changes: false
% 2.77/1.04  git: last_make_outside_of_git: false
% 2.77/1.04  
% 2.77/1.04  ------ 
% 2.77/1.04  
% 2.77/1.04  ------ Input Options
% 2.77/1.04  
% 2.77/1.04  --out_options                           all
% 2.77/1.04  --tptp_safe_out                         true
% 2.77/1.04  --problem_path                          ""
% 2.77/1.04  --include_path                          ""
% 2.77/1.04  --clausifier                            res/vclausify_rel
% 2.77/1.04  --clausifier_options                    --mode clausify
% 2.77/1.04  --stdin                                 false
% 2.77/1.04  --stats_out                             all
% 2.77/1.04  
% 2.77/1.04  ------ General Options
% 2.77/1.04  
% 2.77/1.04  --fof                                   false
% 2.77/1.04  --time_out_real                         305.
% 2.77/1.04  --time_out_virtual                      -1.
% 2.77/1.04  --symbol_type_check                     false
% 2.77/1.04  --clausify_out                          false
% 2.77/1.04  --sig_cnt_out                           false
% 2.77/1.04  --trig_cnt_out                          false
% 2.77/1.04  --trig_cnt_out_tolerance                1.
% 2.77/1.04  --trig_cnt_out_sk_spl                   false
% 2.77/1.04  --abstr_cl_out                          false
% 2.77/1.04  
% 2.77/1.04  ------ Global Options
% 2.77/1.04  
% 2.77/1.04  --schedule                              default
% 2.77/1.04  --add_important_lit                     false
% 2.77/1.04  --prop_solver_per_cl                    1000
% 2.77/1.04  --min_unsat_core                        false
% 2.77/1.04  --soft_assumptions                      false
% 2.77/1.04  --soft_lemma_size                       3
% 2.77/1.04  --prop_impl_unit_size                   0
% 2.77/1.04  --prop_impl_unit                        []
% 2.77/1.04  --share_sel_clauses                     true
% 2.77/1.04  --reset_solvers                         false
% 2.77/1.04  --bc_imp_inh                            [conj_cone]
% 2.77/1.04  --conj_cone_tolerance                   3.
% 2.77/1.04  --extra_neg_conj                        none
% 2.77/1.04  --large_theory_mode                     true
% 2.77/1.04  --prolific_symb_bound                   200
% 2.77/1.04  --lt_threshold                          2000
% 2.77/1.04  --clause_weak_htbl                      true
% 2.77/1.04  --gc_record_bc_elim                     false
% 2.77/1.04  
% 2.77/1.04  ------ Preprocessing Options
% 2.77/1.04  
% 2.77/1.04  --preprocessing_flag                    true
% 2.77/1.04  --time_out_prep_mult                    0.1
% 2.77/1.04  --splitting_mode                        input
% 2.77/1.04  --splitting_grd                         true
% 2.77/1.04  --splitting_cvd                         false
% 2.77/1.04  --splitting_cvd_svl                     false
% 2.77/1.04  --splitting_nvd                         32
% 2.77/1.04  --sub_typing                            true
% 2.77/1.04  --prep_gs_sim                           true
% 2.77/1.04  --prep_unflatten                        true
% 2.77/1.04  --prep_res_sim                          true
% 2.77/1.04  --prep_upred                            true
% 2.77/1.04  --prep_sem_filter                       exhaustive
% 2.77/1.04  --prep_sem_filter_out                   false
% 2.77/1.04  --pred_elim                             true
% 2.77/1.04  --res_sim_input                         true
% 2.77/1.04  --eq_ax_congr_red                       true
% 2.77/1.04  --pure_diseq_elim                       true
% 2.77/1.04  --brand_transform                       false
% 2.77/1.04  --non_eq_to_eq                          false
% 2.77/1.04  --prep_def_merge                        true
% 2.77/1.04  --prep_def_merge_prop_impl              false
% 2.77/1.04  --prep_def_merge_mbd                    true
% 2.77/1.04  --prep_def_merge_tr_red                 false
% 2.77/1.04  --prep_def_merge_tr_cl                  false
% 2.77/1.04  --smt_preprocessing                     true
% 2.77/1.04  --smt_ac_axioms                         fast
% 2.77/1.04  --preprocessed_out                      false
% 2.77/1.04  --preprocessed_stats                    false
% 2.77/1.04  
% 2.77/1.04  ------ Abstraction refinement Options
% 2.77/1.04  
% 2.77/1.04  --abstr_ref                             []
% 2.77/1.04  --abstr_ref_prep                        false
% 2.77/1.04  --abstr_ref_until_sat                   false
% 2.77/1.04  --abstr_ref_sig_restrict                funpre
% 2.77/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.04  --abstr_ref_under                       []
% 2.77/1.04  
% 2.77/1.04  ------ SAT Options
% 2.77/1.04  
% 2.77/1.04  --sat_mode                              false
% 2.77/1.04  --sat_fm_restart_options                ""
% 2.77/1.04  --sat_gr_def                            false
% 2.77/1.04  --sat_epr_types                         true
% 2.77/1.04  --sat_non_cyclic_types                  false
% 2.77/1.04  --sat_finite_models                     false
% 2.77/1.04  --sat_fm_lemmas                         false
% 2.77/1.04  --sat_fm_prep                           false
% 2.77/1.04  --sat_fm_uc_incr                        true
% 2.77/1.04  --sat_out_model                         small
% 2.77/1.04  --sat_out_clauses                       false
% 2.77/1.04  
% 2.77/1.04  ------ QBF Options
% 2.77/1.04  
% 2.77/1.04  --qbf_mode                              false
% 2.77/1.04  --qbf_elim_univ                         false
% 2.77/1.04  --qbf_dom_inst                          none
% 2.77/1.04  --qbf_dom_pre_inst                      false
% 2.77/1.04  --qbf_sk_in                             false
% 2.77/1.04  --qbf_pred_elim                         true
% 2.77/1.04  --qbf_split                             512
% 2.77/1.04  
% 2.77/1.04  ------ BMC1 Options
% 2.77/1.04  
% 2.77/1.04  --bmc1_incremental                      false
% 2.77/1.04  --bmc1_axioms                           reachable_all
% 2.77/1.04  --bmc1_min_bound                        0
% 2.77/1.04  --bmc1_max_bound                        -1
% 2.77/1.04  --bmc1_max_bound_default                -1
% 2.77/1.04  --bmc1_symbol_reachability              true
% 2.77/1.04  --bmc1_property_lemmas                  false
% 2.77/1.04  --bmc1_k_induction                      false
% 2.77/1.04  --bmc1_non_equiv_states                 false
% 2.77/1.04  --bmc1_deadlock                         false
% 2.77/1.04  --bmc1_ucm                              false
% 2.77/1.04  --bmc1_add_unsat_core                   none
% 2.77/1.04  --bmc1_unsat_core_children              false
% 2.77/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.04  --bmc1_out_stat                         full
% 2.77/1.04  --bmc1_ground_init                      false
% 2.77/1.04  --bmc1_pre_inst_next_state              false
% 2.77/1.04  --bmc1_pre_inst_state                   false
% 2.77/1.04  --bmc1_pre_inst_reach_state             false
% 2.77/1.04  --bmc1_out_unsat_core                   false
% 2.77/1.04  --bmc1_aig_witness_out                  false
% 2.77/1.04  --bmc1_verbose                          false
% 2.77/1.04  --bmc1_dump_clauses_tptp                false
% 2.77/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.04  --bmc1_dump_file                        -
% 2.77/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.04  --bmc1_ucm_extend_mode                  1
% 2.77/1.04  --bmc1_ucm_init_mode                    2
% 2.77/1.04  --bmc1_ucm_cone_mode                    none
% 2.77/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.04  --bmc1_ucm_relax_model                  4
% 2.77/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.04  --bmc1_ucm_layered_model                none
% 2.77/1.04  --bmc1_ucm_max_lemma_size               10
% 2.77/1.04  
% 2.77/1.04  ------ AIG Options
% 2.77/1.04  
% 2.77/1.04  --aig_mode                              false
% 2.77/1.04  
% 2.77/1.04  ------ Instantiation Options
% 2.77/1.04  
% 2.77/1.04  --instantiation_flag                    true
% 2.77/1.04  --inst_sos_flag                         false
% 2.77/1.04  --inst_sos_phase                        true
% 2.77/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.04  --inst_lit_sel_side                     num_symb
% 2.77/1.04  --inst_solver_per_active                1400
% 2.77/1.04  --inst_solver_calls_frac                1.
% 2.77/1.04  --inst_passive_queue_type               priority_queues
% 2.77/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.04  --inst_passive_queues_freq              [25;2]
% 2.77/1.04  --inst_dismatching                      true
% 2.77/1.04  --inst_eager_unprocessed_to_passive     true
% 2.77/1.04  --inst_prop_sim_given                   true
% 2.77/1.04  --inst_prop_sim_new                     false
% 2.77/1.04  --inst_subs_new                         false
% 2.77/1.04  --inst_eq_res_simp                      false
% 2.77/1.04  --inst_subs_given                       false
% 2.77/1.04  --inst_orphan_elimination               true
% 2.77/1.04  --inst_learning_loop_flag               true
% 2.77/1.04  --inst_learning_start                   3000
% 2.77/1.04  --inst_learning_factor                  2
% 2.77/1.04  --inst_start_prop_sim_after_learn       3
% 2.77/1.04  --inst_sel_renew                        solver
% 2.77/1.04  --inst_lit_activity_flag                true
% 2.77/1.04  --inst_restr_to_given                   false
% 2.77/1.04  --inst_activity_threshold               500
% 2.77/1.04  --inst_out_proof                        true
% 2.77/1.04  
% 2.77/1.04  ------ Resolution Options
% 2.77/1.04  
% 2.77/1.04  --resolution_flag                       true
% 2.77/1.04  --res_lit_sel                           adaptive
% 2.77/1.04  --res_lit_sel_side                      none
% 2.77/1.04  --res_ordering                          kbo
% 2.77/1.04  --res_to_prop_solver                    active
% 2.77/1.04  --res_prop_simpl_new                    false
% 2.77/1.04  --res_prop_simpl_given                  true
% 2.77/1.04  --res_passive_queue_type                priority_queues
% 2.77/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.04  --res_passive_queues_freq               [15;5]
% 2.77/1.04  --res_forward_subs                      full
% 2.77/1.04  --res_backward_subs                     full
% 2.77/1.04  --res_forward_subs_resolution           true
% 2.77/1.04  --res_backward_subs_resolution          true
% 2.77/1.04  --res_orphan_elimination                true
% 2.77/1.04  --res_time_limit                        2.
% 2.77/1.04  --res_out_proof                         true
% 2.77/1.04  
% 2.77/1.04  ------ Superposition Options
% 2.77/1.04  
% 2.77/1.04  --superposition_flag                    true
% 2.77/1.04  --sup_passive_queue_type                priority_queues
% 2.77/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.04  --demod_completeness_check              fast
% 2.77/1.04  --demod_use_ground                      true
% 2.77/1.04  --sup_to_prop_solver                    passive
% 2.77/1.04  --sup_prop_simpl_new                    true
% 2.77/1.04  --sup_prop_simpl_given                  true
% 2.77/1.04  --sup_fun_splitting                     false
% 2.77/1.04  --sup_smt_interval                      50000
% 2.77/1.04  
% 2.77/1.04  ------ Superposition Simplification Setup
% 2.77/1.04  
% 2.77/1.04  --sup_indices_passive                   []
% 2.77/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.04  --sup_full_bw                           [BwDemod]
% 2.77/1.04  --sup_immed_triv                        [TrivRules]
% 2.77/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.04  --sup_immed_bw_main                     []
% 2.77/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.04  
% 2.77/1.04  ------ Combination Options
% 2.77/1.04  
% 2.77/1.04  --comb_res_mult                         3
% 2.77/1.04  --comb_sup_mult                         2
% 2.77/1.04  --comb_inst_mult                        10
% 2.77/1.04  
% 2.77/1.04  ------ Debug Options
% 2.77/1.04  
% 2.77/1.04  --dbg_backtrace                         false
% 2.77/1.04  --dbg_dump_prop_clauses                 false
% 2.77/1.04  --dbg_dump_prop_clauses_file            -
% 2.77/1.04  --dbg_out_stat                          false
% 2.77/1.04  ------ Parsing...
% 2.77/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.04  
% 2.77/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.77/1.04  
% 2.77/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.04  
% 2.77/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.04  ------ Proving...
% 2.77/1.04  ------ Problem Properties 
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  clauses                                 31
% 2.77/1.04  conjectures                             17
% 2.77/1.04  EPR                                     17
% 2.77/1.04  Horn                                    28
% 2.77/1.04  unary                                   19
% 2.77/1.04  binary                                  2
% 2.77/1.04  lits                                    90
% 2.77/1.04  lits eq                                 8
% 2.77/1.04  fd_pure                                 0
% 2.77/1.04  fd_pseudo                               0
% 2.77/1.04  fd_cond                                 0
% 2.77/1.04  fd_pseudo_cond                          0
% 2.77/1.04  AC symbols                              0
% 2.77/1.04  
% 2.77/1.04  ------ Schedule dynamic 5 is on 
% 2.77/1.04  
% 2.77/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  ------ 
% 2.77/1.04  Current options:
% 2.77/1.04  ------ 
% 2.77/1.04  
% 2.77/1.04  ------ Input Options
% 2.77/1.04  
% 2.77/1.04  --out_options                           all
% 2.77/1.04  --tptp_safe_out                         true
% 2.77/1.04  --problem_path                          ""
% 2.77/1.04  --include_path                          ""
% 2.77/1.04  --clausifier                            res/vclausify_rel
% 2.77/1.04  --clausifier_options                    --mode clausify
% 2.77/1.04  --stdin                                 false
% 2.77/1.04  --stats_out                             all
% 2.77/1.04  
% 2.77/1.04  ------ General Options
% 2.77/1.04  
% 2.77/1.04  --fof                                   false
% 2.77/1.04  --time_out_real                         305.
% 2.77/1.04  --time_out_virtual                      -1.
% 2.77/1.04  --symbol_type_check                     false
% 2.77/1.04  --clausify_out                          false
% 2.77/1.04  --sig_cnt_out                           false
% 2.77/1.04  --trig_cnt_out                          false
% 2.77/1.04  --trig_cnt_out_tolerance                1.
% 2.77/1.04  --trig_cnt_out_sk_spl                   false
% 2.77/1.04  --abstr_cl_out                          false
% 2.77/1.04  
% 2.77/1.04  ------ Global Options
% 2.77/1.04  
% 2.77/1.04  --schedule                              default
% 2.77/1.04  --add_important_lit                     false
% 2.77/1.04  --prop_solver_per_cl                    1000
% 2.77/1.04  --min_unsat_core                        false
% 2.77/1.04  --soft_assumptions                      false
% 2.77/1.04  --soft_lemma_size                       3
% 2.77/1.04  --prop_impl_unit_size                   0
% 2.77/1.04  --prop_impl_unit                        []
% 2.77/1.04  --share_sel_clauses                     true
% 2.77/1.04  --reset_solvers                         false
% 2.77/1.04  --bc_imp_inh                            [conj_cone]
% 2.77/1.04  --conj_cone_tolerance                   3.
% 2.77/1.04  --extra_neg_conj                        none
% 2.77/1.04  --large_theory_mode                     true
% 2.77/1.04  --prolific_symb_bound                   200
% 2.77/1.04  --lt_threshold                          2000
% 2.77/1.04  --clause_weak_htbl                      true
% 2.77/1.04  --gc_record_bc_elim                     false
% 2.77/1.04  
% 2.77/1.04  ------ Preprocessing Options
% 2.77/1.04  
% 2.77/1.04  --preprocessing_flag                    true
% 2.77/1.04  --time_out_prep_mult                    0.1
% 2.77/1.04  --splitting_mode                        input
% 2.77/1.04  --splitting_grd                         true
% 2.77/1.04  --splitting_cvd                         false
% 2.77/1.04  --splitting_cvd_svl                     false
% 2.77/1.04  --splitting_nvd                         32
% 2.77/1.04  --sub_typing                            true
% 2.77/1.04  --prep_gs_sim                           true
% 2.77/1.04  --prep_unflatten                        true
% 2.77/1.04  --prep_res_sim                          true
% 2.77/1.04  --prep_upred                            true
% 2.77/1.04  --prep_sem_filter                       exhaustive
% 2.77/1.04  --prep_sem_filter_out                   false
% 2.77/1.04  --pred_elim                             true
% 2.77/1.04  --res_sim_input                         true
% 2.77/1.04  --eq_ax_congr_red                       true
% 2.77/1.04  --pure_diseq_elim                       true
% 2.77/1.04  --brand_transform                       false
% 2.77/1.04  --non_eq_to_eq                          false
% 2.77/1.04  --prep_def_merge                        true
% 2.77/1.04  --prep_def_merge_prop_impl              false
% 2.77/1.04  --prep_def_merge_mbd                    true
% 2.77/1.04  --prep_def_merge_tr_red                 false
% 2.77/1.04  --prep_def_merge_tr_cl                  false
% 2.77/1.04  --smt_preprocessing                     true
% 2.77/1.04  --smt_ac_axioms                         fast
% 2.77/1.04  --preprocessed_out                      false
% 2.77/1.04  --preprocessed_stats                    false
% 2.77/1.04  
% 2.77/1.04  ------ Abstraction refinement Options
% 2.77/1.04  
% 2.77/1.04  --abstr_ref                             []
% 2.77/1.04  --abstr_ref_prep                        false
% 2.77/1.04  --abstr_ref_until_sat                   false
% 2.77/1.04  --abstr_ref_sig_restrict                funpre
% 2.77/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.04  --abstr_ref_under                       []
% 2.77/1.04  
% 2.77/1.04  ------ SAT Options
% 2.77/1.04  
% 2.77/1.04  --sat_mode                              false
% 2.77/1.04  --sat_fm_restart_options                ""
% 2.77/1.04  --sat_gr_def                            false
% 2.77/1.04  --sat_epr_types                         true
% 2.77/1.04  --sat_non_cyclic_types                  false
% 2.77/1.04  --sat_finite_models                     false
% 2.77/1.04  --sat_fm_lemmas                         false
% 2.77/1.04  --sat_fm_prep                           false
% 2.77/1.04  --sat_fm_uc_incr                        true
% 2.77/1.04  --sat_out_model                         small
% 2.77/1.04  --sat_out_clauses                       false
% 2.77/1.04  
% 2.77/1.04  ------ QBF Options
% 2.77/1.04  
% 2.77/1.04  --qbf_mode                              false
% 2.77/1.04  --qbf_elim_univ                         false
% 2.77/1.04  --qbf_dom_inst                          none
% 2.77/1.04  --qbf_dom_pre_inst                      false
% 2.77/1.04  --qbf_sk_in                             false
% 2.77/1.04  --qbf_pred_elim                         true
% 2.77/1.04  --qbf_split                             512
% 2.77/1.04  
% 2.77/1.04  ------ BMC1 Options
% 2.77/1.04  
% 2.77/1.04  --bmc1_incremental                      false
% 2.77/1.04  --bmc1_axioms                           reachable_all
% 2.77/1.04  --bmc1_min_bound                        0
% 2.77/1.04  --bmc1_max_bound                        -1
% 2.77/1.04  --bmc1_max_bound_default                -1
% 2.77/1.04  --bmc1_symbol_reachability              true
% 2.77/1.04  --bmc1_property_lemmas                  false
% 2.77/1.04  --bmc1_k_induction                      false
% 2.77/1.04  --bmc1_non_equiv_states                 false
% 2.77/1.04  --bmc1_deadlock                         false
% 2.77/1.04  --bmc1_ucm                              false
% 2.77/1.04  --bmc1_add_unsat_core                   none
% 2.77/1.04  --bmc1_unsat_core_children              false
% 2.77/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.04  --bmc1_out_stat                         full
% 2.77/1.04  --bmc1_ground_init                      false
% 2.77/1.04  --bmc1_pre_inst_next_state              false
% 2.77/1.04  --bmc1_pre_inst_state                   false
% 2.77/1.04  --bmc1_pre_inst_reach_state             false
% 2.77/1.04  --bmc1_out_unsat_core                   false
% 2.77/1.04  --bmc1_aig_witness_out                  false
% 2.77/1.04  --bmc1_verbose                          false
% 2.77/1.04  --bmc1_dump_clauses_tptp                false
% 2.77/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.04  --bmc1_dump_file                        -
% 2.77/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.04  --bmc1_ucm_extend_mode                  1
% 2.77/1.04  --bmc1_ucm_init_mode                    2
% 2.77/1.04  --bmc1_ucm_cone_mode                    none
% 2.77/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.04  --bmc1_ucm_relax_model                  4
% 2.77/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.04  --bmc1_ucm_layered_model                none
% 2.77/1.04  --bmc1_ucm_max_lemma_size               10
% 2.77/1.04  
% 2.77/1.04  ------ AIG Options
% 2.77/1.04  
% 2.77/1.04  --aig_mode                              false
% 2.77/1.04  
% 2.77/1.04  ------ Instantiation Options
% 2.77/1.04  
% 2.77/1.04  --instantiation_flag                    true
% 2.77/1.04  --inst_sos_flag                         false
% 2.77/1.04  --inst_sos_phase                        true
% 2.77/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.04  --inst_lit_sel_side                     none
% 2.77/1.04  --inst_solver_per_active                1400
% 2.77/1.04  --inst_solver_calls_frac                1.
% 2.77/1.04  --inst_passive_queue_type               priority_queues
% 2.77/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.04  --inst_passive_queues_freq              [25;2]
% 2.77/1.04  --inst_dismatching                      true
% 2.77/1.04  --inst_eager_unprocessed_to_passive     true
% 2.77/1.04  --inst_prop_sim_given                   true
% 2.77/1.04  --inst_prop_sim_new                     false
% 2.77/1.04  --inst_subs_new                         false
% 2.77/1.04  --inst_eq_res_simp                      false
% 2.77/1.04  --inst_subs_given                       false
% 2.77/1.04  --inst_orphan_elimination               true
% 2.77/1.04  --inst_learning_loop_flag               true
% 2.77/1.04  --inst_learning_start                   3000
% 2.77/1.04  --inst_learning_factor                  2
% 2.77/1.04  --inst_start_prop_sim_after_learn       3
% 2.77/1.04  --inst_sel_renew                        solver
% 2.77/1.04  --inst_lit_activity_flag                true
% 2.77/1.04  --inst_restr_to_given                   false
% 2.77/1.04  --inst_activity_threshold               500
% 2.77/1.04  --inst_out_proof                        true
% 2.77/1.04  
% 2.77/1.04  ------ Resolution Options
% 2.77/1.04  
% 2.77/1.04  --resolution_flag                       false
% 2.77/1.04  --res_lit_sel                           adaptive
% 2.77/1.04  --res_lit_sel_side                      none
% 2.77/1.04  --res_ordering                          kbo
% 2.77/1.04  --res_to_prop_solver                    active
% 2.77/1.04  --res_prop_simpl_new                    false
% 2.77/1.04  --res_prop_simpl_given                  true
% 2.77/1.04  --res_passive_queue_type                priority_queues
% 2.77/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.04  --res_passive_queues_freq               [15;5]
% 2.77/1.04  --res_forward_subs                      full
% 2.77/1.04  --res_backward_subs                     full
% 2.77/1.04  --res_forward_subs_resolution           true
% 2.77/1.04  --res_backward_subs_resolution          true
% 2.77/1.04  --res_orphan_elimination                true
% 2.77/1.04  --res_time_limit                        2.
% 2.77/1.04  --res_out_proof                         true
% 2.77/1.04  
% 2.77/1.04  ------ Superposition Options
% 2.77/1.04  
% 2.77/1.04  --superposition_flag                    true
% 2.77/1.04  --sup_passive_queue_type                priority_queues
% 2.77/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.04  --demod_completeness_check              fast
% 2.77/1.04  --demod_use_ground                      true
% 2.77/1.04  --sup_to_prop_solver                    passive
% 2.77/1.04  --sup_prop_simpl_new                    true
% 2.77/1.04  --sup_prop_simpl_given                  true
% 2.77/1.04  --sup_fun_splitting                     false
% 2.77/1.04  --sup_smt_interval                      50000
% 2.77/1.04  
% 2.77/1.04  ------ Superposition Simplification Setup
% 2.77/1.04  
% 2.77/1.04  --sup_indices_passive                   []
% 2.77/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.04  --sup_full_bw                           [BwDemod]
% 2.77/1.04  --sup_immed_triv                        [TrivRules]
% 2.77/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.04  --sup_immed_bw_main                     []
% 2.77/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.04  
% 2.77/1.04  ------ Combination Options
% 2.77/1.04  
% 2.77/1.04  --comb_res_mult                         3
% 2.77/1.04  --comb_sup_mult                         2
% 2.77/1.04  --comb_inst_mult                        10
% 2.77/1.04  
% 2.77/1.04  ------ Debug Options
% 2.77/1.04  
% 2.77/1.04  --dbg_backtrace                         false
% 2.77/1.04  --dbg_dump_prop_clauses                 false
% 2.77/1.04  --dbg_dump_prop_clauses_file            -
% 2.77/1.04  --dbg_out_stat                          false
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  ------ Proving...
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  % SZS status Theorem for theBenchmark.p
% 2.77/1.04  
% 2.77/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.04  
% 2.77/1.04  fof(f16,conjecture,(
% 2.77/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f17,negated_conjecture,(
% 2.77/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.77/1.04    inference(negated_conjecture,[],[f16])).
% 2.77/1.04  
% 2.77/1.04  fof(f37,plain,(
% 2.77/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.77/1.04    inference(ennf_transformation,[],[f17])).
% 2.77/1.04  
% 2.77/1.04  fof(f38,plain,(
% 2.77/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.77/1.04    inference(flattening,[],[f37])).
% 2.77/1.04  
% 2.77/1.04  fof(f47,plain,(
% 2.77/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f46,plain,(
% 2.77/1.04    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f45,plain,(
% 2.77/1.04    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f44,plain,(
% 2.77/1.04    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f43,plain,(
% 2.77/1.04    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f42,plain,(
% 2.77/1.04    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f41,plain,(
% 2.77/1.04    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.77/1.04    introduced(choice_axiom,[])).
% 2.77/1.04  
% 2.77/1.04  fof(f48,plain,(
% 2.77/1.04    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.77/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f38,f47,f46,f45,f44,f43,f42,f41])).
% 2.77/1.04  
% 2.77/1.04  fof(f83,plain,(
% 2.77/1.04    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f82,plain,(
% 2.77/1.04    sK5 = sK6),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f75,plain,(
% 2.77/1.04    m1_pre_topc(sK3,sK0)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f7,axiom,(
% 2.77/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f24,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f7])).
% 2.77/1.04  
% 2.77/1.04  fof(f55,plain,(
% 2.77/1.04    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f24])).
% 2.77/1.04  
% 2.77/1.04  fof(f68,plain,(
% 2.77/1.04    l1_pre_topc(sK0)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f6,axiom,(
% 2.77/1.04    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f23,plain,(
% 2.77/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f6])).
% 2.77/1.04  
% 2.77/1.04  fof(f54,plain,(
% 2.77/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f23])).
% 2.77/1.04  
% 2.77/1.04  fof(f5,axiom,(
% 2.77/1.04    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f22,plain,(
% 2.77/1.04    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f5])).
% 2.77/1.04  
% 2.77/1.04  fof(f53,plain,(
% 2.77/1.04    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f22])).
% 2.77/1.04  
% 2.77/1.04  fof(f11,axiom,(
% 2.77/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f29,plain,(
% 2.77/1.04    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.77/1.04    inference(ennf_transformation,[],[f11])).
% 2.77/1.04  
% 2.77/1.04  fof(f30,plain,(
% 2.77/1.04    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.77/1.04    inference(flattening,[],[f29])).
% 2.77/1.04  
% 2.77/1.04  fof(f60,plain,(
% 2.77/1.04    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f30])).
% 2.77/1.04  
% 2.77/1.04  fof(f15,axiom,(
% 2.77/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f35,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/1.04    inference(ennf_transformation,[],[f15])).
% 2.77/1.04  
% 2.77/1.04  fof(f36,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/1.04    inference(flattening,[],[f35])).
% 2.77/1.04  
% 2.77/1.04  fof(f40,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/1.04    inference(nnf_transformation,[],[f36])).
% 2.77/1.04  
% 2.77/1.04  fof(f65,plain,(
% 2.77/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f40])).
% 2.77/1.04  
% 2.77/1.04  fof(f85,plain,(
% 2.77/1.04    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/1.04    inference(equality_resolution,[],[f65])).
% 2.77/1.04  
% 2.77/1.04  fof(f77,plain,(
% 2.77/1.04    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f76,plain,(
% 2.77/1.04    v1_funct_1(sK4)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f14,axiom,(
% 2.77/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f33,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.77/1.04    inference(ennf_transformation,[],[f14])).
% 2.77/1.04  
% 2.77/1.04  fof(f34,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.77/1.04    inference(flattening,[],[f33])).
% 2.77/1.04  
% 2.77/1.04  fof(f63,plain,(
% 2.77/1.04    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f34])).
% 2.77/1.04  
% 2.77/1.04  fof(f4,axiom,(
% 2.77/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f20,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.77/1.04    inference(ennf_transformation,[],[f4])).
% 2.77/1.04  
% 2.77/1.04  fof(f21,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.77/1.04    inference(flattening,[],[f20])).
% 2.77/1.04  
% 2.77/1.04  fof(f52,plain,(
% 2.77/1.04    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f21])).
% 2.77/1.04  
% 2.77/1.04  fof(f69,plain,(
% 2.77/1.04    ~v2_struct_0(sK1)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f70,plain,(
% 2.77/1.04    v2_pre_topc(sK1)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f71,plain,(
% 2.77/1.04    l1_pre_topc(sK1)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f74,plain,(
% 2.77/1.04    ~v2_struct_0(sK3)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f78,plain,(
% 2.77/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f2,axiom,(
% 2.77/1.04    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f50,plain,(
% 2.77/1.04    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.77/1.04    inference(cnf_transformation,[],[f2])).
% 2.77/1.04  
% 2.77/1.04  fof(f1,axiom,(
% 2.77/1.04    ! [X0] : k2_subset_1(X0) = X0),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f49,plain,(
% 2.77/1.04    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.77/1.04    inference(cnf_transformation,[],[f1])).
% 2.77/1.04  
% 2.77/1.04  fof(f73,plain,(
% 2.77/1.04    m1_pre_topc(sK2,sK0)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f13,axiom,(
% 2.77/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f32,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f13])).
% 2.77/1.04  
% 2.77/1.04  fof(f62,plain,(
% 2.77/1.04    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f32])).
% 2.77/1.04  
% 2.77/1.04  fof(f12,axiom,(
% 2.77/1.04    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f31,plain,(
% 2.77/1.04    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f12])).
% 2.77/1.04  
% 2.77/1.04  fof(f61,plain,(
% 2.77/1.04    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f31])).
% 2.77/1.04  
% 2.77/1.04  fof(f10,axiom,(
% 2.77/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f28,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f10])).
% 2.77/1.04  
% 2.77/1.04  fof(f39,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(nnf_transformation,[],[f28])).
% 2.77/1.04  
% 2.77/1.04  fof(f58,plain,(
% 2.77/1.04    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f39])).
% 2.77/1.04  
% 2.77/1.04  fof(f79,plain,(
% 2.77/1.04    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f81,plain,(
% 2.77/1.04    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f80,plain,(
% 2.77/1.04    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f3,axiom,(
% 2.77/1.04    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f18,plain,(
% 2.77/1.04    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.77/1.04    inference(ennf_transformation,[],[f3])).
% 2.77/1.04  
% 2.77/1.04  fof(f19,plain,(
% 2.77/1.04    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.77/1.04    inference(flattening,[],[f18])).
% 2.77/1.04  
% 2.77/1.04  fof(f51,plain,(
% 2.77/1.04    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f19])).
% 2.77/1.04  
% 2.77/1.04  fof(f8,axiom,(
% 2.77/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f25,plain,(
% 2.77/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.77/1.04    inference(ennf_transformation,[],[f8])).
% 2.77/1.04  
% 2.77/1.04  fof(f26,plain,(
% 2.77/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.77/1.04    inference(flattening,[],[f25])).
% 2.77/1.04  
% 2.77/1.04  fof(f56,plain,(
% 2.77/1.04    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f26])).
% 2.77/1.04  
% 2.77/1.04  fof(f9,axiom,(
% 2.77/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 2.77/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.77/1.04  
% 2.77/1.04  fof(f27,plain,(
% 2.77/1.04    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.77/1.04    inference(ennf_transformation,[],[f9])).
% 2.77/1.04  
% 2.77/1.04  fof(f57,plain,(
% 2.77/1.04    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 2.77/1.04    inference(cnf_transformation,[],[f27])).
% 2.77/1.04  
% 2.77/1.04  fof(f84,plain,(
% 2.77/1.04    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f72,plain,(
% 2.77/1.04    ~v2_struct_0(sK2)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f67,plain,(
% 2.77/1.04    v2_pre_topc(sK0)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  fof(f66,plain,(
% 2.77/1.04    ~v2_struct_0(sK0)),
% 2.77/1.04    inference(cnf_transformation,[],[f48])).
% 2.77/1.04  
% 2.77/1.04  cnf(c_18,negated_conjecture,
% 2.77/1.04      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 2.77/1.04      inference(cnf_transformation,[],[f83]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1948,plain,
% 2.77/1.04      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_19,negated_conjecture,
% 2.77/1.04      ( sK5 = sK6 ),
% 2.77/1.04      inference(cnf_transformation,[],[f82]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2004,plain,
% 2.77/1.04      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_1948,c_19]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_26,negated_conjecture,
% 2.77/1.04      ( m1_pre_topc(sK3,sK0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1944,plain,
% 2.77/1.04      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_6,plain,
% 2.77/1.04      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f55]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1954,plain,
% 2.77/1.04      ( m1_pre_topc(X0,X1) != iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top
% 2.77/1.04      | l1_pre_topc(X0) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3033,plain,
% 2.77/1.04      ( l1_pre_topc(sK0) != iProver_top
% 2.77/1.04      | l1_pre_topc(sK3) = iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_1944,c_1954]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_33,negated_conjecture,
% 2.77/1.04      ( l1_pre_topc(sK0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f68]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_38,plain,
% 2.77/1.04      ( l1_pre_topc(sK0) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3352,plain,
% 2.77/1.04      ( l1_pre_topc(sK3) = iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_3033,c_38]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5,plain,
% 2.77/1.04      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4,plain,
% 2.77/1.04      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_386,plain,
% 2.77/1.04      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.77/1.04      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1932,plain,
% 2.77/1.04      ( u1_struct_0(X0) = k2_struct_0(X0)
% 2.77/1.04      | l1_pre_topc(X0) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3357,plain,
% 2.77/1.04      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_3352,c_1932]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_11,plain,
% 2.77/1.04      ( v3_pre_topc(k2_struct_0(X0),X0)
% 2.77/1.04      | ~ l1_pre_topc(X0)
% 2.77/1.04      | ~ v2_pre_topc(X0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_15,plain,
% 2.77/1.04      ( r1_tmap_1(X0,X1,X2,X3)
% 2.77/1.04      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.77/1.04      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.77/1.04      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.77/1.04      | ~ v3_pre_topc(X6,X0)
% 2.77/1.04      | ~ m1_pre_topc(X4,X5)
% 2.77/1.04      | ~ m1_pre_topc(X4,X0)
% 2.77/1.04      | ~ m1_pre_topc(X0,X5)
% 2.77/1.04      | ~ r2_hidden(X3,X6)
% 2.77/1.04      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.77/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.77/1.04      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.77/1.04      | ~ v1_funct_1(X2)
% 2.77/1.04      | v2_struct_0(X5)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X4)
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | ~ l1_pre_topc(X5)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X5)
% 2.77/1.04      | ~ v2_pre_topc(X1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f85]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_24,negated_conjecture,
% 2.77/1.04      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.77/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_483,plain,
% 2.77/1.04      ( r1_tmap_1(X0,X1,X2,X3)
% 2.77/1.04      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.77/1.04      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.77/1.04      | ~ v3_pre_topc(X6,X0)
% 2.77/1.04      | ~ m1_pre_topc(X4,X5)
% 2.77/1.04      | ~ m1_pre_topc(X4,X0)
% 2.77/1.04      | ~ m1_pre_topc(X0,X5)
% 2.77/1.04      | ~ r2_hidden(X3,X6)
% 2.77/1.04      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.77/1.04      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.77/1.04      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.77/1.04      | ~ v1_funct_1(X2)
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X5)
% 2.77/1.04      | v2_struct_0(X4)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X5)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X5)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.77/1.04      | sK4 != X2 ),
% 2.77/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_484,plain,
% 2.77/1.04      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.77/1.04      | ~ v3_pre_topc(X5,X3)
% 2.77/1.04      | ~ m1_pre_topc(X0,X2)
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ r2_hidden(X4,X5)
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | ~ v1_funct_1(sK4)
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 2.77/1.04      inference(unflattening,[status(thm)],[c_483]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_25,negated_conjecture,
% 2.77/1.04      ( v1_funct_1(sK4) ),
% 2.77/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_488,plain,
% 2.77/1.04      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ r2_hidden(X4,X5)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X0,X2)
% 2.77/1.04      | ~ v3_pre_topc(X5,X3)
% 2.77/1.04      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_484,c_25]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_489,plain,
% 2.77/1.04      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.77/1.04      | ~ v3_pre_topc(X5,X3)
% 2.77/1.04      | ~ m1_pre_topc(X0,X2)
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ r2_hidden(X4,X5)
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 2.77/1.04      inference(renaming,[status(thm)],[c_488]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_14,plain,
% 2.77/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.04      | ~ m1_pre_topc(X2,X0)
% 2.77/1.04      | m1_pre_topc(X2,X1)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f63]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_538,plain,
% 2.77/1.04      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.77/1.04      | ~ v3_pre_topc(X5,X3)
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ r2_hidden(X4,X5)
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 2.77/1.04      inference(forward_subsumption_resolution,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_489,c_14]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_642,plain,
% 2.77/1.04      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ r2_hidden(X4,X5)
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | ~ l1_pre_topc(X6)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X6)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | X3 != X6
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.77/1.04      | k2_struct_0(X6) != X5 ),
% 2.77/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_538]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_643,plain,
% 2.77/1.04      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ r2_hidden(X4,k2_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ l1_pre_topc(X3)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X3)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 2.77/1.04      inference(unflattening,[status(thm)],[c_642]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3,plain,
% 2.77/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | v2_pre_topc(X0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f52]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_691,plain,
% 2.77/1.04      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.77/1.04      | r1_tmap_1(X3,X1,sK4,X4)
% 2.77/1.04      | ~ r1_tarski(k2_struct_0(X3),u1_struct_0(X0))
% 2.77/1.04      | ~ m1_pre_topc(X0,X3)
% 2.77/1.04      | ~ m1_pre_topc(X3,X2)
% 2.77/1.04      | ~ r2_hidden(X4,k2_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.77/1.04      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.77/1.04      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 2.77/1.04      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.77/1.04      | v2_struct_0(X0)
% 2.77/1.04      | v2_struct_0(X1)
% 2.77/1.04      | v2_struct_0(X2)
% 2.77/1.04      | v2_struct_0(X3)
% 2.77/1.04      | ~ l1_pre_topc(X1)
% 2.77/1.04      | ~ l1_pre_topc(X2)
% 2.77/1.04      | ~ v2_pre_topc(X1)
% 2.77/1.04      | ~ v2_pre_topc(X2)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 2.77/1.04      inference(forward_subsumption_resolution,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_643,c_3,c_6]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1931,plain,
% 2.77/1.04      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.77/1.04      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.77/1.04      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
% 2.77/1.04      | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X2,X1) != iProver_top
% 2.77/1.04      | m1_pre_topc(X1,X3) != iProver_top
% 2.77/1.04      | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.77/1.04      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(X2) = iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X3) = iProver_top
% 2.77/1.04      | l1_pre_topc(X0) != iProver_top
% 2.77/1.04      | l1_pre_topc(X3) != iProver_top
% 2.77/1.04      | v2_pre_topc(X0) != iProver_top
% 2.77/1.04      | v2_pre_topc(X3) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2712,plain,
% 2.77/1.04      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 2.77/1.04      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 2.77/1.04      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,X2) != iProver_top
% 2.77/1.04      | m1_pre_topc(X1,X0) != iProver_top
% 2.77/1.04      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(X2) = iProver_top
% 2.77/1.04      | v2_struct_0(sK1) = iProver_top
% 2.77/1.04      | l1_pre_topc(X2) != iProver_top
% 2.77/1.04      | l1_pre_topc(sK1) != iProver_top
% 2.77/1.04      | v2_pre_topc(X2) != iProver_top
% 2.77/1.04      | v2_pre_topc(sK1) != iProver_top ),
% 2.77/1.04      inference(equality_resolution,[status(thm)],[c_1931]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_32,negated_conjecture,
% 2.77/1.04      ( ~ v2_struct_0(sK1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_39,plain,
% 2.77/1.04      ( v2_struct_0(sK1) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_31,negated_conjecture,
% 2.77/1.04      ( v2_pre_topc(sK1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_40,plain,
% 2.77/1.04      ( v2_pre_topc(sK1) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_30,negated_conjecture,
% 2.77/1.04      ( l1_pre_topc(sK1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_41,plain,
% 2.77/1.04      ( l1_pre_topc(sK1) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5130,plain,
% 2.77/1.04      ( v2_pre_topc(X2) != iProver_top
% 2.77/1.04      | v2_struct_0(X2) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X1,X0) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,X2) != iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 2.77/1.04      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 2.77/1.04      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.77/1.04      | l1_pre_topc(X2) != iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_2712,c_39,c_40,c_41]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5131,plain,
% 2.77/1.04      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 2.77/1.04      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 2.77/1.04      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,X2) != iProver_top
% 2.77/1.04      | m1_pre_topc(X1,X0) != iProver_top
% 2.77/1.04      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(X2) = iProver_top
% 2.77/1.04      | l1_pre_topc(X2) != iProver_top
% 2.77/1.04      | v2_pre_topc(X2) != iProver_top ),
% 2.77/1.04      inference(renaming,[status(thm)],[c_5130]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1940,plain,
% 2.77/1.04      ( l1_pre_topc(sK1) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2828,plain,
% 2.77/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_1940,c_1932]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5134,plain,
% 2.77/1.04      ( u1_struct_0(X0) != k2_struct_0(sK3)
% 2.77/1.04      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 2.77/1.04      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,X2) != iProver_top
% 2.77/1.04      | m1_pre_topc(X1,X0) != iProver_top
% 2.77/1.04      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(X2) = iProver_top
% 2.77/1.04      | l1_pre_topc(X2) != iProver_top
% 2.77/1.04      | v2_pre_topc(X2) != iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_5131,c_2828,c_3357]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5155,plain,
% 2.77/1.04      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 2.77/1.04      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,X1) != iProver_top
% 2.77/1.04      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(sK3) = iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top
% 2.77/1.04      | v2_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_3357,c_5134]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5239,plain,
% 2.77/1.04      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 2.77/1.04      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,X1) != iProver_top
% 2.77/1.04      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.77/1.04      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(sK3) = iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top
% 2.77/1.04      | v2_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_5155,c_3357]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_27,negated_conjecture,
% 2.77/1.04      ( ~ v2_struct_0(sK3) ),
% 2.77/1.04      inference(cnf_transformation,[],[f74]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_44,plain,
% 2.77/1.04      ( v2_struct_0(sK3) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_23,negated_conjecture,
% 2.77/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.77/1.04      inference(cnf_transformation,[],[f78]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1945,plain,
% 2.77/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3157,plain,
% 2.77/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 2.77/1.04      inference(demodulation,[status(thm)],[c_2828,c_1945]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4085,plain,
% 2.77/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 2.77/1.04      inference(demodulation,[status(thm)],[c_3357,c_3157]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_12490,plain,
% 2.77/1.04      ( v2_struct_0(X0) = iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 2.77/1.04      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,X1) != iProver_top
% 2.77/1.04      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top
% 2.77/1.04      | v2_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_5239,c_44,c_4085]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_12491,plain,
% 2.77/1.04      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 2.77/1.04      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,X1) != iProver_top
% 2.77/1.04      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top
% 2.77/1.04      | v2_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(renaming,[status(thm)],[c_12490]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1,plain,
% 2.77/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.77/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1957,plain,
% 2.77/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_0,plain,
% 2.77/1.04      ( k2_subset_1(X0) = X0 ),
% 2.77/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1989,plain,
% 2.77/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_1957,c_0]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_12509,plain,
% 2.77/1.04      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 2.77/1.04      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,X1) != iProver_top
% 2.77/1.04      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.77/1.04      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | v2_struct_0(X1) = iProver_top
% 2.77/1.04      | v2_struct_0(X0) = iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top
% 2.77/1.04      | v2_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(forward_subsumption_resolution,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_12491,c_1989]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_12513,plain,
% 2.77/1.04      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.77/1.04      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 2.77/1.04      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | v2_struct_0(sK0) = iProver_top
% 2.77/1.04      | v2_struct_0(sK2) = iProver_top
% 2.77/1.04      | l1_pre_topc(sK0) != iProver_top
% 2.77/1.04      | v2_pre_topc(sK0) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_2004,c_12509]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_28,negated_conjecture,
% 2.77/1.04      ( m1_pre_topc(sK2,sK0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1942,plain,
% 2.77/1.04      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3034,plain,
% 2.77/1.04      ( l1_pre_topc(sK0) != iProver_top
% 2.77/1.04      | l1_pre_topc(sK2) = iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_1942,c_1954]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3359,plain,
% 2.77/1.04      ( l1_pre_topc(sK2) = iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_3034,c_38]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3364,plain,
% 2.77/1.04      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_3359,c_1932]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_12526,plain,
% 2.77/1.04      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 2.77/1.04      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.77/1.04      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
% 2.77/1.04      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 2.77/1.04      | v2_struct_0(sK0) = iProver_top
% 2.77/1.04      | v2_struct_0(sK2) = iProver_top
% 2.77/1.04      | l1_pre_topc(sK0) != iProver_top
% 2.77/1.04      | v2_pre_topc(sK0) != iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_12513,c_3364]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_13,plain,
% 2.77/1.04      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.77/1.04      | ~ m1_pre_topc(X0,X1)
% 2.77/1.04      | ~ l1_pre_topc(X1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f62]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1951,plain,
% 2.77/1.04      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.77/1.04      | m1_pre_topc(X0,X1) != iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4096,plain,
% 2.77/1.04      ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,X0) != iProver_top
% 2.77/1.04      | l1_pre_topc(X0) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_3357,c_1951]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_5909,plain,
% 2.77/1.04      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 2.77/1.04      | m1_pre_topc(sK3,sK2) != iProver_top
% 2.77/1.04      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_3364,c_4096]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_12,plain,
% 2.77/1.04      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1952,plain,
% 2.77/1.04      ( m1_pre_topc(X0,X0) = iProver_top
% 2.77/1.04      | l1_pre_topc(X0) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_10,plain,
% 2.77/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.04      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.77/1.04      | ~ l1_pre_topc(X0)
% 2.77/1.04      | ~ l1_pre_topc(X1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_182,plain,
% 2.77/1.04      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.77/1.04      | ~ m1_pre_topc(X0,X1)
% 2.77/1.04      | ~ l1_pre_topc(X1) ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_10,c_6]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_183,plain,
% 2.77/1.04      ( ~ m1_pre_topc(X0,X1)
% 2.77/1.04      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.77/1.04      | ~ l1_pre_topc(X1) ),
% 2.77/1.04      inference(renaming,[status(thm)],[c_182]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1934,plain,
% 2.77/1.04      ( m1_pre_topc(X0,X1) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4410,plain,
% 2.77/1.04      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK2) != iProver_top
% 2.77/1.04      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_3364,c_1934]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_22,negated_conjecture,
% 2.77/1.04      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 2.77/1.04      inference(cnf_transformation,[],[f79]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4233,plain,
% 2.77/1.04      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 2.77/1.04      inference(demodulation,[status(thm)],[c_3364,c_22]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4448,plain,
% 2.77/1.04      ( m1_pre_topc(X0,sK2) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) = iProver_top
% 2.77/1.04      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_4410,c_4233]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4596,plain,
% 2.77/1.04      ( m1_pre_topc(X0,sK3) = iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK2) != iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_4448,c_38,c_3034]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4597,plain,
% 2.77/1.04      ( m1_pre_topc(X0,sK2) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) = iProver_top ),
% 2.77/1.04      inference(renaming,[status(thm)],[c_4596]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4604,plain,
% 2.77/1.04      ( m1_pre_topc(sK2,sK3) = iProver_top
% 2.77/1.04      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_1952,c_4597]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_20,negated_conjecture,
% 2.77/1.04      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.77/1.04      inference(cnf_transformation,[],[f81]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1947,plain,
% 2.77/1.04      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1984,plain,
% 2.77/1.04      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.77/1.04      inference(light_normalisation,[status(thm)],[c_1947,c_19]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4232,plain,
% 2.77/1.04      ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
% 2.77/1.04      inference(demodulation,[status(thm)],[c_3364,c_1984]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_21,negated_conjecture,
% 2.77/1.04      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.77/1.04      inference(cnf_transformation,[],[f80]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1946,plain,
% 2.77/1.04      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4086,plain,
% 2.77/1.04      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(demodulation,[status(thm)],[c_3357,c_1946]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2,plain,
% 2.77/1.04      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f51]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1956,plain,
% 2.77/1.04      ( r2_hidden(X0,X1) = iProver_top
% 2.77/1.04      | m1_subset_1(X0,X1) != iProver_top
% 2.77/1.04      | v1_xboole_0(X1) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3049,plain,
% 2.77/1.04      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 2.77/1.04      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_1946,c_1956]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_49,plain,
% 2.77/1.04      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2233,plain,
% 2.77/1.04      ( r2_hidden(sK5,u1_struct_0(sK3))
% 2.77/1.04      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.77/1.04      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.77/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2234,plain,
% 2.77/1.04      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 2.77/1.04      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 2.77/1.04      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_7,plain,
% 2.77/1.04      ( v2_struct_0(X0)
% 2.77/1.04      | ~ l1_struct_0(X0)
% 2.77/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.77/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_372,plain,
% 2.77/1.04      ( v2_struct_0(X0)
% 2.77/1.04      | ~ l1_pre_topc(X0)
% 2.77/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.77/1.04      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2315,plain,
% 2.77/1.04      ( v2_struct_0(sK3)
% 2.77/1.04      | ~ l1_pre_topc(sK3)
% 2.77/1.04      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.77/1.04      inference(instantiation,[status(thm)],[c_372]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_2316,plain,
% 2.77/1.04      ( v2_struct_0(sK3) = iProver_top
% 2.77/1.04      | l1_pre_topc(sK3) != iProver_top
% 2.77/1.04      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3455,plain,
% 2.77/1.04      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_3049,c_38,c_44,c_49,c_2234,c_2316,c_3033]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_4084,plain,
% 2.77/1.04      ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
% 2.77/1.04      inference(demodulation,[status(thm)],[c_3357,c_3455]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_8,plain,
% 2.77/1.04      ( m1_pre_topc(X0,X1)
% 2.77/1.04      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.77/1.04      | ~ l1_pre_topc(X1) ),
% 2.77/1.04      inference(cnf_transformation,[],[f57]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_1953,plain,
% 2.77/1.04      ( m1_pre_topc(X0,X1) = iProver_top
% 2.77/1.04      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 2.77/1.04      | l1_pre_topc(X1) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3725,plain,
% 2.77/1.04      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | l1_pre_topc(sK2) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_22,c_1953]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3863,plain,
% 2.77/1.04      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK2) = iProver_top ),
% 2.77/1.04      inference(global_propositional_subsumption,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_3725,c_38,c_3034]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3864,plain,
% 2.77/1.04      ( m1_pre_topc(X0,sK2) = iProver_top
% 2.77/1.04      | m1_pre_topc(X0,sK3) != iProver_top ),
% 2.77/1.04      inference(renaming,[status(thm)],[c_3863]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_3871,plain,
% 2.77/1.04      ( m1_pre_topc(sK3,sK2) = iProver_top
% 2.77/1.04      | l1_pre_topc(sK3) != iProver_top ),
% 2.77/1.04      inference(superposition,[status(thm)],[c_1952,c_3864]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_17,negated_conjecture,
% 2.77/1.04      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 2.77/1.04      inference(cnf_transformation,[],[f84]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_52,plain,
% 2.77/1.04      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_45,plain,
% 2.77/1.04      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_29,negated_conjecture,
% 2.77/1.04      ( ~ v2_struct_0(sK2) ),
% 2.77/1.04      inference(cnf_transformation,[],[f72]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_42,plain,
% 2.77/1.04      ( v2_struct_0(sK2) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_34,negated_conjecture,
% 2.77/1.04      ( v2_pre_topc(sK0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_37,plain,
% 2.77/1.04      ( v2_pre_topc(sK0) = iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_35,negated_conjecture,
% 2.77/1.04      ( ~ v2_struct_0(sK0) ),
% 2.77/1.04      inference(cnf_transformation,[],[f66]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(c_36,plain,
% 2.77/1.04      ( v2_struct_0(sK0) != iProver_top ),
% 2.77/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.77/1.04  
% 2.77/1.04  cnf(contradiction,plain,
% 2.77/1.04      ( $false ),
% 2.77/1.04      inference(minisat,
% 2.77/1.04                [status(thm)],
% 2.77/1.04                [c_12526,c_5909,c_4604,c_4232,c_4086,c_4084,c_3871,
% 2.77/1.04                 c_3034,c_3033,c_52,c_45,c_42,c_38,c_37,c_36]) ).
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.04  
% 2.77/1.04  ------                               Statistics
% 2.77/1.04  
% 2.77/1.04  ------ General
% 2.77/1.04  
% 2.77/1.04  abstr_ref_over_cycles:                  0
% 2.77/1.04  abstr_ref_under_cycles:                 0
% 2.77/1.04  gc_basic_clause_elim:                   0
% 2.77/1.04  forced_gc_time:                         0
% 2.77/1.04  parsing_time:                           0.045
% 2.77/1.04  unif_index_cands_time:                  0.
% 2.77/1.04  unif_index_add_time:                    0.
% 2.77/1.04  orderings_time:                         0.
% 2.77/1.04  out_proof_time:                         0.013
% 2.77/1.04  total_time:                             0.524
% 2.77/1.04  num_of_symbols:                         59
% 2.77/1.04  num_of_terms:                           6199
% 2.77/1.04  
% 2.77/1.04  ------ Preprocessing
% 2.77/1.04  
% 2.77/1.04  num_of_splits:                          0
% 2.77/1.04  num_of_split_atoms:                     0
% 2.77/1.04  num_of_reused_defs:                     0
% 2.77/1.04  num_eq_ax_congr_red:                    12
% 2.77/1.04  num_of_sem_filtered_clauses:            1
% 2.77/1.04  num_of_subtypes:                        0
% 2.77/1.04  monotx_restored_types:                  0
% 2.77/1.04  sat_num_of_epr_types:                   0
% 2.77/1.04  sat_num_of_non_cyclic_types:            0
% 2.77/1.04  sat_guarded_non_collapsed_types:        0
% 2.77/1.04  num_pure_diseq_elim:                    0
% 2.77/1.04  simp_replaced_by:                       0
% 2.77/1.04  res_preprocessed:                       163
% 2.77/1.04  prep_upred:                             0
% 2.77/1.04  prep_unflattend:                        21
% 2.77/1.04  smt_new_axioms:                         0
% 2.77/1.04  pred_elim_cands:                        9
% 2.77/1.04  pred_elim:                              4
% 2.77/1.04  pred_elim_cl:                           4
% 2.77/1.04  pred_elim_cycles:                       12
% 2.77/1.04  merged_defs:                            0
% 2.77/1.04  merged_defs_ncl:                        0
% 2.77/1.04  bin_hyper_res:                          0
% 2.77/1.04  prep_cycles:                            4
% 2.77/1.04  pred_elim_time:                         0.069
% 2.77/1.04  splitting_time:                         0.
% 2.77/1.04  sem_filter_time:                        0.
% 2.77/1.04  monotx_time:                            0.001
% 2.77/1.04  subtype_inf_time:                       0.
% 2.77/1.04  
% 2.77/1.04  ------ Problem properties
% 2.77/1.04  
% 2.77/1.04  clauses:                                31
% 2.77/1.04  conjectures:                            17
% 2.77/1.04  epr:                                    17
% 2.77/1.04  horn:                                   28
% 2.77/1.04  ground:                                 17
% 2.77/1.04  unary:                                  19
% 2.77/1.04  binary:                                 2
% 2.77/1.04  lits:                                   90
% 2.77/1.04  lits_eq:                                8
% 2.77/1.04  fd_pure:                                0
% 2.77/1.04  fd_pseudo:                              0
% 2.77/1.04  fd_cond:                                0
% 2.77/1.04  fd_pseudo_cond:                         0
% 2.77/1.04  ac_symbols:                             0
% 2.77/1.04  
% 2.77/1.04  ------ Propositional Solver
% 2.77/1.04  
% 2.77/1.04  prop_solver_calls:                      30
% 2.77/1.04  prop_fast_solver_calls:                 2546
% 2.77/1.04  smt_solver_calls:                       0
% 2.77/1.04  smt_fast_solver_calls:                  0
% 2.77/1.04  prop_num_of_clauses:                    3810
% 2.77/1.04  prop_preprocess_simplified:             7935
% 2.77/1.04  prop_fo_subsumed:                       106
% 2.77/1.04  prop_solver_time:                       0.
% 2.77/1.04  smt_solver_time:                        0.
% 2.77/1.04  smt_fast_solver_time:                   0.
% 2.77/1.04  prop_fast_solver_time:                  0.
% 2.77/1.04  prop_unsat_core_time:                   0.
% 2.77/1.04  
% 2.77/1.04  ------ QBF
% 2.77/1.04  
% 2.77/1.04  qbf_q_res:                              0
% 2.77/1.04  qbf_num_tautologies:                    0
% 2.77/1.04  qbf_prep_cycles:                        0
% 2.77/1.04  
% 2.77/1.04  ------ BMC1
% 2.77/1.04  
% 2.77/1.04  bmc1_current_bound:                     -1
% 2.77/1.04  bmc1_last_solved_bound:                 -1
% 2.77/1.04  bmc1_unsat_core_size:                   -1
% 2.77/1.04  bmc1_unsat_core_parents_size:           -1
% 2.77/1.04  bmc1_merge_next_fun:                    0
% 2.77/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.04  
% 2.77/1.04  ------ Instantiation
% 2.77/1.04  
% 2.77/1.04  inst_num_of_clauses:                    1111
% 2.77/1.04  inst_num_in_passive:                    145
% 2.77/1.04  inst_num_in_active:                     678
% 2.77/1.04  inst_num_in_unprocessed:                288
% 2.77/1.04  inst_num_of_loops:                      720
% 2.77/1.04  inst_num_of_learning_restarts:          0
% 2.77/1.04  inst_num_moves_active_passive:          38
% 2.77/1.04  inst_lit_activity:                      0
% 2.77/1.04  inst_lit_activity_moves:                0
% 2.77/1.04  inst_num_tautologies:                   0
% 2.77/1.04  inst_num_prop_implied:                  0
% 2.77/1.04  inst_num_existing_simplified:           0
% 2.77/1.04  inst_num_eq_res_simplified:             0
% 2.77/1.04  inst_num_child_elim:                    0
% 2.77/1.04  inst_num_of_dismatching_blockings:      374
% 2.77/1.04  inst_num_of_non_proper_insts:           1424
% 2.77/1.04  inst_num_of_duplicates:                 0
% 2.77/1.04  inst_inst_num_from_inst_to_res:         0
% 2.77/1.04  inst_dismatching_checking_time:         0.
% 2.77/1.04  
% 2.77/1.04  ------ Resolution
% 2.77/1.04  
% 2.77/1.04  res_num_of_clauses:                     0
% 2.77/1.04  res_num_in_passive:                     0
% 2.77/1.04  res_num_in_active:                      0
% 2.77/1.04  res_num_of_loops:                       167
% 2.77/1.04  res_forward_subset_subsumed:            155
% 2.77/1.04  res_backward_subset_subsumed:           0
% 2.77/1.04  res_forward_subsumed:                   0
% 2.77/1.04  res_backward_subsumed:                  0
% 2.77/1.04  res_forward_subsumption_resolution:     6
% 2.77/1.04  res_backward_subsumption_resolution:    0
% 2.77/1.04  res_clause_to_clause_subsumption:       1241
% 2.77/1.04  res_orphan_elimination:                 0
% 2.77/1.04  res_tautology_del:                      223
% 2.77/1.04  res_num_eq_res_simplified:              0
% 2.77/1.04  res_num_sel_changes:                    0
% 2.77/1.04  res_moves_from_active_to_pass:          0
% 2.77/1.04  
% 2.77/1.04  ------ Superposition
% 2.77/1.04  
% 2.77/1.04  sup_time_total:                         0.
% 2.77/1.04  sup_time_generating:                    0.
% 2.77/1.04  sup_time_sim_full:                      0.
% 2.77/1.04  sup_time_sim_immed:                     0.
% 2.77/1.04  
% 2.77/1.04  sup_num_of_clauses:                     203
% 2.77/1.04  sup_num_in_active:                      134
% 2.77/1.04  sup_num_in_passive:                     69
% 2.77/1.04  sup_num_of_loops:                       143
% 2.77/1.04  sup_fw_superposition:                   176
% 2.77/1.04  sup_bw_superposition:                   135
% 2.77/1.04  sup_immediate_simplified:               111
% 2.77/1.04  sup_given_eliminated:                   0
% 2.77/1.04  comparisons_done:                       0
% 2.77/1.04  comparisons_avoided:                    0
% 2.77/1.04  
% 2.77/1.04  ------ Simplifications
% 2.77/1.04  
% 2.77/1.04  
% 2.77/1.04  sim_fw_subset_subsumed:                 47
% 2.77/1.04  sim_bw_subset_subsumed:                 17
% 2.77/1.04  sim_fw_subsumed:                        26
% 2.77/1.04  sim_bw_subsumed:                        0
% 2.77/1.04  sim_fw_subsumption_res:                 11
% 2.77/1.04  sim_bw_subsumption_res:                 0
% 2.77/1.04  sim_tautology_del:                      27
% 2.77/1.04  sim_eq_tautology_del:                   0
% 2.77/1.04  sim_eq_res_simp:                        0
% 2.77/1.04  sim_fw_demodulated:                     0
% 2.77/1.04  sim_bw_demodulated:                     10
% 2.77/1.04  sim_light_normalised:                   65
% 2.77/1.04  sim_joinable_taut:                      0
% 2.77/1.04  sim_joinable_simp:                      0
% 2.77/1.04  sim_ac_normalised:                      0
% 2.77/1.04  sim_smt_subsumption:                    0
% 2.77/1.04  
%------------------------------------------------------------------------------
