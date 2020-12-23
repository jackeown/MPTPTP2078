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
% DateTime   : Thu Dec  3 12:23:28 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 994 expanded)
%              Number of clauses        :   98 ( 207 expanded)
%              Number of leaves         :   23 ( 444 expanded)
%              Depth                    :   15
%              Number of atoms          :  875 (13766 expanded)
%              Number of equality atoms :  242 (2070 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   38 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f41,f52,f51,f50,f49,f48,f47,f46])).

fof(f92,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f45])).

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
    inference(equality_resolution,[],[f74])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1172,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1240,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1172,c_23])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
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

cnf(c_1175,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1176,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1404,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1175,c_1176])).

cnf(c_7098,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1404])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1166,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1186,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2511,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1186])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1874,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

cnf(c_1875,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_2719,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2511,c_42,c_1875])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1190,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3915,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_1190])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1876,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

cnf(c_1877,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1184,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3155,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1184])).

cnf(c_4587,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3915,c_42,c_46,c_1877,c_3155])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1181,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4883,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1181])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2589,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2594,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2589])).

cnf(c_4885,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1181])).

cnf(c_5044,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(X0,X1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4883,c_42,c_1877,c_2594,c_4885])).

cnf(c_5045,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_5044])).

cnf(c_5050,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4587,c_5045])).

cnf(c_7116,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7098,c_5050])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1187,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2724,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_1187])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1188,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2782,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2724,c_1188])).

cnf(c_12,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1179,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3347,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_1179])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3027,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_30])).

cnf(c_3028,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3027])).

cnf(c_3555,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3347,c_41,c_42,c_1875,c_3028])).

cnf(c_14,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_16,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_297,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_298,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_1155,plain,
    ( v1_tsep_1(X0,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_5561,plain,
    ( v1_tsep_1(sK2,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5050,c_1155])).

cnf(c_7052,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3555,c_5561])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1177,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_284,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_4])).

cnf(c_285,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_1156,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_2985,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1156])).

cnf(c_3141,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2985,c_42,c_1877])).

cnf(c_3142,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3141])).

cnf(c_3149,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_3142])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_56,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_52,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_50,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_49,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7116,c_7052,c_3149,c_3028,c_1877,c_1875,c_56,c_53,c_52,c_51,c_50,c_49,c_48,c_46,c_45,c_44,c_43,c_42,c_41,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.66/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/0.99  
% 3.66/0.99  ------  iProver source info
% 3.66/0.99  
% 3.66/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.66/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/0.99  git: non_committed_changes: false
% 3.66/0.99  git: last_make_outside_of_git: false
% 3.66/0.99  
% 3.66/0.99  ------ 
% 3.66/0.99  ------ Parsing...
% 3.66/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/0.99  
% 3.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.66/0.99  
% 3.66/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/0.99  
% 3.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/0.99  ------ Proving...
% 3.66/0.99  ------ Problem Properties 
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  clauses                                 39
% 3.66/0.99  conjectures                             19
% 3.66/0.99  EPR                                     18
% 3.66/0.99  Horn                                    36
% 3.66/0.99  unary                                   19
% 3.66/0.99  binary                                  4
% 3.66/0.99  lits                                    115
% 3.66/0.99  lits eq                                 8
% 3.66/0.99  fd_pure                                 0
% 3.66/0.99  fd_pseudo                               0
% 3.66/0.99  fd_cond                                 0
% 3.66/0.99  fd_pseudo_cond                          2
% 3.66/0.99  AC symbols                              0
% 3.66/0.99  
% 3.66/0.99  ------ Input Options Time Limit: Unbounded
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  ------ 
% 3.66/0.99  Current options:
% 3.66/0.99  ------ 
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  ------ Proving...
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  % SZS status Theorem for theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  fof(f16,conjecture,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f17,negated_conjecture,(
% 3.66/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.66/0.99    inference(negated_conjecture,[],[f16])).
% 3.66/0.99  
% 3.66/0.99  fof(f40,plain,(
% 3.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f17])).
% 3.66/0.99  
% 3.66/0.99  fof(f41,plain,(
% 3.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.66/0.99    inference(flattening,[],[f40])).
% 3.66/0.99  
% 3.66/0.99  fof(f52,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f51,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f50,plain,(
% 3.66/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f49,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f48,plain,(
% 3.66/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f47,plain,(
% 3.66/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f46,plain,(
% 3.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f53,plain,(
% 3.66/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.66/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f41,f52,f51,f50,f49,f48,f47,f46])).
% 3.66/0.99  
% 3.66/0.99  fof(f92,plain,(
% 3.66/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f91,plain,(
% 3.66/0.99    sK5 = sK6),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f15,axiom,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f38,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f15])).
% 3.66/0.99  
% 3.66/0.99  fof(f39,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.99    inference(flattening,[],[f38])).
% 3.66/0.99  
% 3.66/0.99  fof(f45,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.99    inference(nnf_transformation,[],[f39])).
% 3.66/0.99  
% 3.66/0.99  fof(f74,plain,(
% 3.66/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f45])).
% 3.66/0.99  
% 3.66/0.99  fof(f97,plain,(
% 3.66/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.99    inference(equality_resolution,[],[f74])).
% 3.66/0.99  
% 3.66/0.99  fof(f14,axiom,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f36,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f14])).
% 3.66/0.99  
% 3.66/0.99  fof(f37,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.99    inference(flattening,[],[f36])).
% 3.66/0.99  
% 3.66/0.99  fof(f72,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f37])).
% 3.66/0.99  
% 3.66/0.99  fof(f84,plain,(
% 3.66/0.99    m1_pre_topc(sK3,sK0)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f5,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f24,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f5])).
% 3.66/0.99  
% 3.66/0.99  fof(f58,plain,(
% 3.66/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f24])).
% 3.66/0.99  
% 3.66/0.99  fof(f77,plain,(
% 3.66/0.99    l1_pre_topc(sK0)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f1,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f18,plain,(
% 3.66/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f1])).
% 3.66/0.99  
% 3.66/0.99  fof(f19,plain,(
% 3.66/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(flattening,[],[f18])).
% 3.66/0.99  
% 3.66/0.99  fof(f54,plain,(
% 3.66/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f19])).
% 3.66/0.99  
% 3.66/0.99  fof(f81,plain,(
% 3.66/0.99    ~v2_struct_0(sK2)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f82,plain,(
% 3.66/0.99    m1_pre_topc(sK2,sK0)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f88,plain,(
% 3.66/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f7,axiom,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f26,plain,(
% 3.66/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f7])).
% 3.66/0.99  
% 3.66/0.99  fof(f27,plain,(
% 3.66/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.99    inference(flattening,[],[f26])).
% 3.66/0.99  
% 3.66/0.99  fof(f61,plain,(
% 3.66/0.99    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f27])).
% 3.66/0.99  
% 3.66/0.99  fof(f8,axiom,(
% 3.66/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f28,plain,(
% 3.66/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.66/0.99    inference(ennf_transformation,[],[f8])).
% 3.66/0.99  
% 3.66/0.99  fof(f62,plain,(
% 3.66/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.66/0.99    inference(cnf_transformation,[],[f28])).
% 3.66/0.99  
% 3.66/0.99  fof(f6,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f25,plain,(
% 3.66/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f6])).
% 3.66/0.99  
% 3.66/0.99  fof(f59,plain,(
% 3.66/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f25])).
% 3.66/0.99  
% 3.66/0.99  fof(f4,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f23,plain,(
% 3.66/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f4])).
% 3.66/0.99  
% 3.66/0.99  fof(f57,plain,(
% 3.66/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f23])).
% 3.66/0.99  
% 3.66/0.99  fof(f3,axiom,(
% 3.66/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f22,plain,(
% 3.66/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f3])).
% 3.66/0.99  
% 3.66/0.99  fof(f56,plain,(
% 3.66/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f22])).
% 3.66/0.99  
% 3.66/0.99  fof(f10,axiom,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f30,plain,(
% 3.66/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f10])).
% 3.66/0.99  
% 3.66/0.99  fof(f31,plain,(
% 3.66/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.99    inference(flattening,[],[f30])).
% 3.66/0.99  
% 3.66/0.99  fof(f66,plain,(
% 3.66/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f31])).
% 3.66/0.99  
% 3.66/0.99  fof(f76,plain,(
% 3.66/0.99    v2_pre_topc(sK0)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f2,axiom,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f20,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f2])).
% 3.66/0.99  
% 3.66/0.99  fof(f21,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.99    inference(flattening,[],[f20])).
% 3.66/0.99  
% 3.66/0.99  fof(f55,plain,(
% 3.66/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f21])).
% 3.66/0.99  
% 3.66/0.99  fof(f11,axiom,(
% 3.66/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f32,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f11])).
% 3.66/0.99  
% 3.66/0.99  fof(f33,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.99    inference(flattening,[],[f32])).
% 3.66/0.99  
% 3.66/0.99  fof(f43,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.99    inference(nnf_transformation,[],[f33])).
% 3.66/0.99  
% 3.66/0.99  fof(f44,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.66/0.99    inference(flattening,[],[f43])).
% 3.66/0.99  
% 3.66/0.99  fof(f68,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f44])).
% 3.66/0.99  
% 3.66/0.99  fof(f95,plain,(
% 3.66/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.66/0.99    inference(equality_resolution,[],[f68])).
% 3.66/0.99  
% 3.66/0.99  fof(f12,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f34,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f12])).
% 3.66/0.99  
% 3.66/0.99  fof(f70,plain,(
% 3.66/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f34])).
% 3.66/0.99  
% 3.66/0.99  fof(f13,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f35,plain,(
% 3.66/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f13])).
% 3.66/0.99  
% 3.66/0.99  fof(f71,plain,(
% 3.66/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f35])).
% 3.66/0.99  
% 3.66/0.99  fof(f9,axiom,(
% 3.66/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.66/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f29,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f9])).
% 3.66/0.99  
% 3.66/0.99  fof(f42,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.66/0.99    inference(nnf_transformation,[],[f29])).
% 3.66/0.99  
% 3.66/0.99  fof(f64,plain,(
% 3.66/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f42])).
% 3.66/0.99  
% 3.66/0.99  fof(f93,plain,(
% 3.66/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f89,plain,(
% 3.66/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f87,plain,(
% 3.66/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f86,plain,(
% 3.66/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f85,plain,(
% 3.66/0.99    v1_funct_1(sK4)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f83,plain,(
% 3.66/0.99    ~v2_struct_0(sK3)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f80,plain,(
% 3.66/0.99    l1_pre_topc(sK1)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f79,plain,(
% 3.66/0.99    v2_pre_topc(sK1)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f78,plain,(
% 3.66/0.99    ~v2_struct_0(sK1)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  fof(f75,plain,(
% 3.66/0.99    ~v2_struct_0(sK0)),
% 3.66/0.99    inference(cnf_transformation,[],[f53])).
% 3.66/0.99  
% 3.66/0.99  cnf(c_22,negated_conjecture,
% 3.66/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.66/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1172,plain,
% 3.66/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_23,negated_conjecture,
% 3.66/0.99      ( sK5 = sK6 ),
% 3.66/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1240,plain,
% 3.66/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.66/0.99      inference(light_normalisation,[status(thm)],[c_1172,c_23]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_19,plain,
% 3.66/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.66/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.66/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.66/0.99      | ~ v1_tsep_1(X4,X0)
% 3.66/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.66/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/0.99      | ~ m1_pre_topc(X0,X5)
% 3.66/0.99      | ~ m1_pre_topc(X4,X0)
% 3.66/0.99      | ~ m1_pre_topc(X4,X5)
% 3.66/0.99      | ~ v1_funct_1(X2)
% 3.66/0.99      | v2_struct_0(X5)
% 3.66/0.99      | v2_struct_0(X1)
% 3.66/0.99      | v2_struct_0(X4)
% 3.66/0.99      | v2_struct_0(X0)
% 3.66/0.99      | ~ v2_pre_topc(X5)
% 3.66/0.99      | ~ v2_pre_topc(X1)
% 3.66/0.99      | ~ l1_pre_topc(X5)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1175,plain,
% 3.66/0.99      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.66/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.66/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.66/0.99      | v1_tsep_1(X4,X0) != iProver_top
% 3.66/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.66/0.99      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.66/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.66/0.99      | m1_pre_topc(X0,X5) != iProver_top
% 3.66/0.99      | m1_pre_topc(X4,X0) != iProver_top
% 3.66/0.99      | m1_pre_topc(X4,X5) != iProver_top
% 3.66/0.99      | v1_funct_1(X2) != iProver_top
% 3.66/0.99      | v2_struct_0(X5) = iProver_top
% 3.66/0.99      | v2_struct_0(X1) = iProver_top
% 3.66/0.99      | v2_struct_0(X4) = iProver_top
% 3.66/0.99      | v2_struct_0(X0) = iProver_top
% 3.66/0.99      | v2_pre_topc(X5) != iProver_top
% 3.66/0.99      | v2_pre_topc(X1) != iProver_top
% 3.66/0.99      | l1_pre_topc(X5) != iProver_top
% 3.66/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_18,plain,
% 3.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ m1_pre_topc(X2,X0)
% 3.66/0.99      | m1_pre_topc(X2,X1)
% 3.66/0.99      | ~ v2_pre_topc(X1)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1176,plain,
% 3.66/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.66/0.99      | m1_pre_topc(X2,X1) = iProver_top
% 3.66/0.99      | v2_pre_topc(X1) != iProver_top
% 3.66/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1404,plain,
% 3.66/0.99      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.66/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.66/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.66/0.99      | v1_tsep_1(X4,X0) != iProver_top
% 3.66/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.66/0.99      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.66/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.66/0.99      | m1_pre_topc(X0,X5) != iProver_top
% 3.66/0.99      | m1_pre_topc(X4,X0) != iProver_top
% 3.66/0.99      | v1_funct_1(X2) != iProver_top
% 3.66/0.99      | v2_struct_0(X5) = iProver_top
% 3.66/0.99      | v2_struct_0(X1) = iProver_top
% 3.66/0.99      | v2_struct_0(X4) = iProver_top
% 3.66/0.99      | v2_struct_0(X0) = iProver_top
% 3.66/0.99      | v2_pre_topc(X5) != iProver_top
% 3.66/0.99      | v2_pre_topc(X1) != iProver_top
% 3.66/0.99      | l1_pre_topc(X5) != iProver_top
% 3.66/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.99      inference(forward_subsumption_resolution,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_1175,c_1176]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7098,plain,
% 3.66/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.66/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.66/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.66/0.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.66/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.66/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.66/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.66/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.66/0.99      | v1_funct_1(sK4) != iProver_top
% 3.66/0.99      | v2_struct_0(sK0) = iProver_top
% 3.66/0.99      | v2_struct_0(sK2) = iProver_top
% 3.66/0.99      | v2_struct_0(sK1) = iProver_top
% 3.66/0.99      | v2_struct_0(sK3) = iProver_top
% 3.66/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.66/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1240,c_1404]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_30,negated_conjecture,
% 3.66/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1166,plain,
% 3.66/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4,plain,
% 3.66/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1186,plain,
% 3.66/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.99      | l1_pre_topc(X1) != iProver_top
% 3.66/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2511,plain,
% 3.66/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1166,c_1186]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_37,negated_conjecture,
% 3.66/0.99      ( l1_pre_topc(sK0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_42,plain,
% 3.66/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1874,plain,
% 3.66/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.66/0.99      inference(resolution,[status(thm)],[c_4,c_30]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1875,plain,
% 3.66/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2719,plain,
% 3.66/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_2511,c_42,c_1875]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_0,plain,
% 3.66/0.99      ( ~ l1_pre_topc(X0)
% 3.66/0.99      | ~ v1_pre_topc(X0)
% 3.66/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.66/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1190,plain,
% 3.66/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.66/0.99      | l1_pre_topc(X0) != iProver_top
% 3.66/0.99      | v1_pre_topc(X0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3915,plain,
% 3.66/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 3.66/0.99      | v1_pre_topc(sK3) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2719,c_1190]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_33,negated_conjecture,
% 3.66/0.99      ( ~ v2_struct_0(sK2) ),
% 3.66/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_46,plain,
% 3.66/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_32,negated_conjecture,
% 3.66/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1876,plain,
% 3.66/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.66/0.99      inference(resolution,[status(thm)],[c_4,c_32]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1877,plain,
% 3.66/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_26,negated_conjecture,
% 3.66/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.66/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_6,plain,
% 3.66/0.99      ( v2_struct_0(X0)
% 3.66/0.99      | ~ l1_pre_topc(X0)
% 3.66/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.66/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1184,plain,
% 3.66/0.99      ( v2_struct_0(X0) = iProver_top
% 3.66/0.99      | l1_pre_topc(X0) != iProver_top
% 3.66/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3155,plain,
% 3.66/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.66/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.66/0.99      | v1_pre_topc(sK3) = iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_26,c_1184]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4587,plain,
% 3.66/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_3915,c_42,c_46,c_1877,c_3155]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_9,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.66/0.99      | X2 = X1
% 3.66/0.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1181,plain,
% 3.66/0.99      ( X0 = X1
% 3.66/0.99      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.66/0.99      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4883,plain,
% 3.66/0.99      ( g1_pre_topc(X0,X1) != sK3
% 3.66/0.99      | u1_struct_0(sK2) = X0
% 3.66/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_26,c_1181]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_5,plain,
% 3.66/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.66/0.99      | ~ l1_pre_topc(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2589,plain,
% 3.66/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.66/0.99      | ~ l1_pre_topc(sK2) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2594,plain,
% 3.66/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.66/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_2589]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4885,plain,
% 3.66/0.99      ( g1_pre_topc(X0,X1) != sK3
% 3.66/0.99      | u1_struct_0(sK2) = X0
% 3.66/0.99      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_26,c_1181]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_5044,plain,
% 3.66/0.99      ( u1_struct_0(sK2) = X0 | g1_pre_topc(X0,X1) != sK3 ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_4883,c_42,c_1877,c_2594,c_4885]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_5045,plain,
% 3.66/0.99      ( g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0 ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_5044]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_5050,plain,
% 3.66/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_4587,c_5045]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7116,plain,
% 3.66/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.66/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.66/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.66/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.66/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.66/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.66/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.66/0.99      | v1_funct_1(sK4) != iProver_top
% 3.66/0.99      | v2_struct_0(sK0) = iProver_top
% 3.66/0.99      | v2_struct_0(sK2) = iProver_top
% 3.66/0.99      | v2_struct_0(sK1) = iProver_top
% 3.66/0.99      | v2_struct_0(sK3) = iProver_top
% 3.66/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.66/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.66/0.99      inference(light_normalisation,[status(thm)],[c_7098,c_5050]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3,plain,
% 3.66/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1187,plain,
% 3.66/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2724,plain,
% 3.66/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2719,c_1187]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2,plain,
% 3.66/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1188,plain,
% 3.66/0.99      ( k2_struct_0(X0) = u1_struct_0(X0)
% 3.66/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2782,plain,
% 3.66/0.99      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2724,c_1188]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_12,plain,
% 3.66/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.66/0.99      | ~ v2_pre_topc(X0)
% 3.66/0.99      | ~ l1_pre_topc(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1179,plain,
% 3.66/0.99      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 3.66/0.99      | v2_pre_topc(X0) != iProver_top
% 3.66/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3347,plain,
% 3.66/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
% 3.66/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2782,c_1179]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_38,negated_conjecture,
% 3.66/0.99      ( v2_pre_topc(sK0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_41,plain,
% 3.66/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1,plain,
% 3.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ v2_pre_topc(X1)
% 3.66/0.99      | v2_pre_topc(X0)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3027,plain,
% 3.66/0.99      ( ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 3.66/0.99      inference(resolution,[status(thm)],[c_1,c_30]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3028,plain,
% 3.66/0.99      ( v2_pre_topc(sK0) != iProver_top
% 3.66/0.99      | v2_pre_topc(sK3) = iProver_top
% 3.66/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_3027]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3555,plain,
% 3.66/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_3347,c_41,c_42,c_1875,c_3028]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_14,plain,
% 3.66/0.99      ( v1_tsep_1(X0,X1)
% 3.66/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.66/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.66/0.99      | ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ v2_pre_topc(X1)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_16,plain,
% 3.66/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.66/0.99      | ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_297,plain,
% 3.66/0.99      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.66/0.99      | v1_tsep_1(X0,X1)
% 3.66/0.99      | ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ v2_pre_topc(X1)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_14,c_16]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_298,plain,
% 3.66/0.99      ( v1_tsep_1(X0,X1)
% 3.66/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.66/0.99      | ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ v2_pre_topc(X1)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_297]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1155,plain,
% 3.66/0.99      ( v1_tsep_1(X0,X1) = iProver_top
% 3.66/0.99      | v3_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 3.66/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.99      | v2_pre_topc(X1) != iProver_top
% 3.66/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_5561,plain,
% 3.66/0.99      ( v1_tsep_1(sK2,X0) = iProver_top
% 3.66/0.99      | v3_pre_topc(u1_struct_0(sK3),X0) != iProver_top
% 3.66/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.66/0.99      | v2_pre_topc(X0) != iProver_top
% 3.66/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_5050,c_1155]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7052,plain,
% 3.66/0.99      ( v1_tsep_1(sK2,sK3) = iProver_top
% 3.66/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.66/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.66/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_3555,c_5561]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_17,plain,
% 3.66/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1177,plain,
% 3.66/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.66/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_11,plain,
% 3.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.66/0.99      | ~ l1_pre_topc(X0)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_284,plain,
% 3.66/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.66/0.99      | ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_11,c_4]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_285,plain,
% 3.66/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.66/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.66/0.99      | ~ l1_pre_topc(X1) ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_284]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1156,plain,
% 3.66/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.66/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.66/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2985,plain,
% 3.66/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.66/0.99      | m1_pre_topc(X0,sK3) = iProver_top
% 3.66/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_26,c_1156]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3141,plain,
% 3.66/0.99      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.66/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_2985,c_42,c_1877]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3142,plain,
% 3.66/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.66/0.99      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_3141]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3149,plain,
% 3.66/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.66/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1177,c_3142]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_21,negated_conjecture,
% 3.66/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.66/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_56,plain,
% 3.66/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_25,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.66/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_53,plain,
% 3.66/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_27,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.66/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_52,plain,
% 3.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_28,negated_conjecture,
% 3.66/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.66/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_51,plain,
% 3.66/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_29,negated_conjecture,
% 3.66/0.99      ( v1_funct_1(sK4) ),
% 3.66/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_50,plain,
% 3.66/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_49,plain,
% 3.66/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_31,negated_conjecture,
% 3.66/0.99      ( ~ v2_struct_0(sK3) ),
% 3.66/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_48,plain,
% 3.66/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_34,negated_conjecture,
% 3.66/0.99      ( l1_pre_topc(sK1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_45,plain,
% 3.66/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_35,negated_conjecture,
% 3.66/0.99      ( v2_pre_topc(sK1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_44,plain,
% 3.66/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_36,negated_conjecture,
% 3.66/0.99      ( ~ v2_struct_0(sK1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_43,plain,
% 3.66/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_39,negated_conjecture,
% 3.66/0.99      ( ~ v2_struct_0(sK0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_40,plain,
% 3.66/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(contradiction,plain,
% 3.66/0.99      ( $false ),
% 3.66/0.99      inference(minisat,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_7116,c_7052,c_3149,c_3028,c_1877,c_1875,c_56,c_53,
% 3.66/0.99                 c_52,c_51,c_50,c_49,c_48,c_46,c_45,c_44,c_43,c_42,c_41,
% 3.66/0.99                 c_40]) ).
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  ------                               Statistics
% 3.66/0.99  
% 3.66/0.99  ------ Selected
% 3.66/0.99  
% 3.66/0.99  total_time:                             0.286
% 3.66/0.99  
%------------------------------------------------------------------------------
