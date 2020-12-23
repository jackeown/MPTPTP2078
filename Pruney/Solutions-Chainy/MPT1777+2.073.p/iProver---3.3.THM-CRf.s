%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:40 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  234 (1805 expanded)
%              Number of clauses        :  143 ( 439 expanded)
%              Number of leaves         :   23 ( 781 expanded)
%              Depth                    :   29
%              Number of atoms          : 1313 (24867 expanded)
%              Number of equality atoms :  414 (3805 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f80,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f90,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

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

fof(f72,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f84,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
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

fof(f69,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_875,plain,
    ( v3_pre_topc(k2_struct_0(X0_54),X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1408,plain,
    ( v3_pre_topc(k2_struct_0(X0_54),X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_858,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1423,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_870,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1413,plain,
    ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_870])).

cnf(c_2812,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1413])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_862,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2816,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2812,c_862])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2827,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2816,c_37,c_38,c_39,c_43])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_871,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X2_54,X1_54)
    | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1412,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54)) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_873,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1410,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_2321,plain,
    ( m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_1410])).

cnf(c_3387,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | m1_pre_topc(sK3,k1_tsep_1(X1_54,sK2,X0_54)) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_54,sK2,X0_54)) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_2321])).

cnf(c_3751,plain,
    ( v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(sK3,k1_tsep_1(X1_54,sK2,X0_54)) = iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_54,sK2,X0_54)) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3387,c_43])).

cnf(c_3752,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | m1_pre_topc(sK3,k1_tsep_1(X1_54,sK2,X0_54)) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_54,sK2,X0_54)) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3751])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_877,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1406,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_2140,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1406])).

cnf(c_2501,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2140,c_39])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_369,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_850,plain,
    ( ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_1431,plain,
    ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_3400,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2501,c_1431])).

cnf(c_11,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_872,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1411,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_3922,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_1411])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_876,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1407,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_5308,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3922,c_1407])).

cnf(c_12743,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK2,X1_54)))) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(k1_tsep_1(X0_54,sK2,X1_54)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_5308])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1748,plain,
    ( ~ m1_pre_topc(sK3,X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_1980,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_1981,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_3382,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2827,c_1412])).

cnf(c_16316,plain,
    ( l1_pre_topc(k1_tsep_1(X0_54,sK2,X1_54)) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK2,X1_54)))) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12743,c_37,c_38,c_39,c_43,c_44,c_46,c_1981,c_3382])).

cnf(c_16317,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK2,X1_54)))) = iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(sK2,X0_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(k1_tsep_1(X0_54,sK2,X1_54)) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_16316])).

cnf(c_16322,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2827,c_16317])).

cnf(c_860,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1421,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_2139,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1406])).

cnf(c_2429,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2139,c_39,c_46,c_1981])).

cnf(c_3399,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2429,c_1431])).

cnf(c_16329,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16322,c_2827,c_3399])).

cnf(c_3826,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_1411])).

cnf(c_5288,plain,
    ( m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3826,c_39,c_46,c_1981])).

cnf(c_5289,plain,
    ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5288])).

cnf(c_5294,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3400,c_5289])).

cnf(c_16386,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16329,c_37,c_38,c_39,c_43,c_44,c_3382,c_5294])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_874,plain,
    ( ~ v3_pre_topc(X0_55,X0_54)
    | v3_pre_topc(X0_55,X1_54)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1409,plain,
    ( v3_pre_topc(X0_55,X0_54) != iProver_top
    | v3_pre_topc(X0_55,X1_54) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_3825,plain,
    ( v3_pre_topc(X0_55,X0_54) != iProver_top
    | v3_pre_topc(X0_55,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_1409])).

cnf(c_3822,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3399,c_1407])).

cnf(c_20587,plain,
    ( v3_pre_topc(X0_55,sK3) = iProver_top
    | v3_pre_topc(X0_55,X0_54) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3825,c_3822])).

cnf(c_20588,plain,
    ( v3_pre_topc(X0_55,X0_54) != iProver_top
    | v3_pre_topc(X0_55,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_20587])).

cnf(c_20597,plain,
    ( v3_pre_topc(k2_struct_0(sK2),X0_54) != iProver_top
    | v3_pre_topc(k2_struct_0(sK2),sK3) = iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_16386,c_20588])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_866,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1417,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_866])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_865,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1435,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1417,c_865])).

cnf(c_9,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_198,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_11])).

cnf(c_199,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f96])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_452,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_453,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_457,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_26])).

cnf(c_458,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_501,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_458,c_15])).

cnf(c_524,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X5),X6)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
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
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_199,c_501])).

cnf(c_525,plain,
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_569,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(u1_struct_0(X0),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_525,c_0,c_3])).

cnf(c_849,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
    | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
    | ~ v3_pre_topc(u1_struct_0(X0_54),X3_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X2_54)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_1432,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK3)
    | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X2_54),X1_54) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_2134,plain,
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
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1432])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2582,plain,
    ( v2_pre_topc(X2_54) != iProver_top
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
    | l1_pre_topc(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_40,c_41,c_42])).

cnf(c_2583,plain,
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
    | l1_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2582])).

cnf(c_2586,plain,
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
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2583])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2668,plain,
    ( v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_45,c_49])).

cnf(c_2669,plain,
    ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2668])).

cnf(c_2674,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_2669])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_53,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_864,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1418,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_1434,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1418,c_865])).

cnf(c_3143,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2674,c_37,c_38,c_39,c_43,c_46,c_50,c_53,c_1434])).

cnf(c_3144,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3143])).

cnf(c_3914,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3400,c_3144])).

cnf(c_21221,plain,
    ( v3_pre_topc(k2_struct_0(sK2),X0_54) != iProver_top
    | m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20597,c_37,c_38,c_39,c_43,c_44,c_3382,c_3914])).

cnf(c_21227,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_21221])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_869,plain,
    ( m1_pre_topc(X0_54,X0_54)
    | ~ l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1414,plain,
    ( m1_pre_topc(X0_54,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_2426,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_2321])).

cnf(c_878,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1405,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_1701,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1405])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21227,c_2426,c_2140,c_1701,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:34:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.59/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.48  
% 7.59/1.48  ------  iProver source info
% 7.59/1.48  
% 7.59/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.48  git: non_committed_changes: false
% 7.59/1.48  git: last_make_outside_of_git: false
% 7.59/1.48  
% 7.59/1.48  ------ 
% 7.59/1.48  
% 7.59/1.48  ------ Input Options
% 7.59/1.48  
% 7.59/1.48  --out_options                           all
% 7.59/1.48  --tptp_safe_out                         true
% 7.59/1.48  --problem_path                          ""
% 7.59/1.48  --include_path                          ""
% 7.59/1.48  --clausifier                            res/vclausify_rel
% 7.59/1.48  --clausifier_options                    ""
% 7.59/1.48  --stdin                                 false
% 7.59/1.48  --stats_out                             all
% 7.59/1.48  
% 7.59/1.48  ------ General Options
% 7.59/1.48  
% 7.59/1.48  --fof                                   false
% 7.59/1.48  --time_out_real                         305.
% 7.59/1.48  --time_out_virtual                      -1.
% 7.59/1.48  --symbol_type_check                     false
% 7.59/1.48  --clausify_out                          false
% 7.59/1.48  --sig_cnt_out                           false
% 7.59/1.48  --trig_cnt_out                          false
% 7.59/1.48  --trig_cnt_out_tolerance                1.
% 7.59/1.48  --trig_cnt_out_sk_spl                   false
% 7.59/1.48  --abstr_cl_out                          false
% 7.59/1.48  
% 7.59/1.48  ------ Global Options
% 7.59/1.48  
% 7.59/1.48  --schedule                              default
% 7.59/1.48  --add_important_lit                     false
% 7.59/1.48  --prop_solver_per_cl                    1000
% 7.59/1.48  --min_unsat_core                        false
% 7.59/1.48  --soft_assumptions                      false
% 7.59/1.48  --soft_lemma_size                       3
% 7.59/1.48  --prop_impl_unit_size                   0
% 7.59/1.48  --prop_impl_unit                        []
% 7.59/1.48  --share_sel_clauses                     true
% 7.59/1.48  --reset_solvers                         false
% 7.59/1.48  --bc_imp_inh                            [conj_cone]
% 7.59/1.48  --conj_cone_tolerance                   3.
% 7.59/1.48  --extra_neg_conj                        none
% 7.59/1.48  --large_theory_mode                     true
% 7.59/1.48  --prolific_symb_bound                   200
% 7.59/1.48  --lt_threshold                          2000
% 7.59/1.48  --clause_weak_htbl                      true
% 7.59/1.48  --gc_record_bc_elim                     false
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing Options
% 7.59/1.48  
% 7.59/1.48  --preprocessing_flag                    true
% 7.59/1.48  --time_out_prep_mult                    0.1
% 7.59/1.48  --splitting_mode                        input
% 7.59/1.48  --splitting_grd                         true
% 7.59/1.48  --splitting_cvd                         false
% 7.59/1.48  --splitting_cvd_svl                     false
% 7.59/1.48  --splitting_nvd                         32
% 7.59/1.48  --sub_typing                            true
% 7.59/1.48  --prep_gs_sim                           true
% 7.59/1.48  --prep_unflatten                        true
% 7.59/1.48  --prep_res_sim                          true
% 7.59/1.48  --prep_upred                            true
% 7.59/1.48  --prep_sem_filter                       exhaustive
% 7.59/1.48  --prep_sem_filter_out                   false
% 7.59/1.48  --pred_elim                             true
% 7.59/1.48  --res_sim_input                         true
% 7.59/1.48  --eq_ax_congr_red                       true
% 7.59/1.48  --pure_diseq_elim                       true
% 7.59/1.48  --brand_transform                       false
% 7.59/1.48  --non_eq_to_eq                          false
% 7.59/1.48  --prep_def_merge                        true
% 7.59/1.48  --prep_def_merge_prop_impl              false
% 7.59/1.48  --prep_def_merge_mbd                    true
% 7.59/1.48  --prep_def_merge_tr_red                 false
% 7.59/1.48  --prep_def_merge_tr_cl                  false
% 7.59/1.48  --smt_preprocessing                     true
% 7.59/1.48  --smt_ac_axioms                         fast
% 7.59/1.48  --preprocessed_out                      false
% 7.59/1.48  --preprocessed_stats                    false
% 7.59/1.48  
% 7.59/1.48  ------ Abstraction refinement Options
% 7.59/1.48  
% 7.59/1.48  --abstr_ref                             []
% 7.59/1.48  --abstr_ref_prep                        false
% 7.59/1.48  --abstr_ref_until_sat                   false
% 7.59/1.48  --abstr_ref_sig_restrict                funpre
% 7.59/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.48  --abstr_ref_under                       []
% 7.59/1.48  
% 7.59/1.48  ------ SAT Options
% 7.59/1.48  
% 7.59/1.48  --sat_mode                              false
% 7.59/1.48  --sat_fm_restart_options                ""
% 7.59/1.48  --sat_gr_def                            false
% 7.59/1.48  --sat_epr_types                         true
% 7.59/1.48  --sat_non_cyclic_types                  false
% 7.59/1.48  --sat_finite_models                     false
% 7.59/1.48  --sat_fm_lemmas                         false
% 7.59/1.48  --sat_fm_prep                           false
% 7.59/1.48  --sat_fm_uc_incr                        true
% 7.59/1.48  --sat_out_model                         small
% 7.59/1.48  --sat_out_clauses                       false
% 7.59/1.48  
% 7.59/1.48  ------ QBF Options
% 7.59/1.48  
% 7.59/1.48  --qbf_mode                              false
% 7.59/1.48  --qbf_elim_univ                         false
% 7.59/1.48  --qbf_dom_inst                          none
% 7.59/1.48  --qbf_dom_pre_inst                      false
% 7.59/1.48  --qbf_sk_in                             false
% 7.59/1.48  --qbf_pred_elim                         true
% 7.59/1.48  --qbf_split                             512
% 7.59/1.48  
% 7.59/1.48  ------ BMC1 Options
% 7.59/1.48  
% 7.59/1.48  --bmc1_incremental                      false
% 7.59/1.48  --bmc1_axioms                           reachable_all
% 7.59/1.48  --bmc1_min_bound                        0
% 7.59/1.48  --bmc1_max_bound                        -1
% 7.59/1.48  --bmc1_max_bound_default                -1
% 7.59/1.48  --bmc1_symbol_reachability              true
% 7.59/1.48  --bmc1_property_lemmas                  false
% 7.59/1.48  --bmc1_k_induction                      false
% 7.59/1.48  --bmc1_non_equiv_states                 false
% 7.59/1.48  --bmc1_deadlock                         false
% 7.59/1.48  --bmc1_ucm                              false
% 7.59/1.48  --bmc1_add_unsat_core                   none
% 7.59/1.48  --bmc1_unsat_core_children              false
% 7.59/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.48  --bmc1_out_stat                         full
% 7.59/1.48  --bmc1_ground_init                      false
% 7.59/1.48  --bmc1_pre_inst_next_state              false
% 7.59/1.48  --bmc1_pre_inst_state                   false
% 7.59/1.48  --bmc1_pre_inst_reach_state             false
% 7.59/1.48  --bmc1_out_unsat_core                   false
% 7.59/1.48  --bmc1_aig_witness_out                  false
% 7.59/1.48  --bmc1_verbose                          false
% 7.59/1.48  --bmc1_dump_clauses_tptp                false
% 7.59/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.48  --bmc1_dump_file                        -
% 7.59/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.48  --bmc1_ucm_extend_mode                  1
% 7.59/1.48  --bmc1_ucm_init_mode                    2
% 7.59/1.48  --bmc1_ucm_cone_mode                    none
% 7.59/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.48  --bmc1_ucm_relax_model                  4
% 7.59/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.48  --bmc1_ucm_layered_model                none
% 7.59/1.48  --bmc1_ucm_max_lemma_size               10
% 7.59/1.48  
% 7.59/1.48  ------ AIG Options
% 7.59/1.48  
% 7.59/1.48  --aig_mode                              false
% 7.59/1.48  
% 7.59/1.48  ------ Instantiation Options
% 7.59/1.48  
% 7.59/1.48  --instantiation_flag                    true
% 7.59/1.48  --inst_sos_flag                         true
% 7.59/1.48  --inst_sos_phase                        true
% 7.59/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel_side                     num_symb
% 7.59/1.48  --inst_solver_per_active                1400
% 7.59/1.48  --inst_solver_calls_frac                1.
% 7.59/1.48  --inst_passive_queue_type               priority_queues
% 7.59/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.48  --inst_passive_queues_freq              [25;2]
% 7.59/1.48  --inst_dismatching                      true
% 7.59/1.48  --inst_eager_unprocessed_to_passive     true
% 7.59/1.48  --inst_prop_sim_given                   true
% 7.59/1.48  --inst_prop_sim_new                     false
% 7.59/1.48  --inst_subs_new                         false
% 7.59/1.48  --inst_eq_res_simp                      false
% 7.59/1.48  --inst_subs_given                       false
% 7.59/1.48  --inst_orphan_elimination               true
% 7.59/1.48  --inst_learning_loop_flag               true
% 7.59/1.48  --inst_learning_start                   3000
% 7.59/1.48  --inst_learning_factor                  2
% 7.59/1.48  --inst_start_prop_sim_after_learn       3
% 7.59/1.48  --inst_sel_renew                        solver
% 7.59/1.48  --inst_lit_activity_flag                true
% 7.59/1.48  --inst_restr_to_given                   false
% 7.59/1.48  --inst_activity_threshold               500
% 7.59/1.48  --inst_out_proof                        true
% 7.59/1.48  
% 7.59/1.48  ------ Resolution Options
% 7.59/1.48  
% 7.59/1.48  --resolution_flag                       true
% 7.59/1.48  --res_lit_sel                           adaptive
% 7.59/1.48  --res_lit_sel_side                      none
% 7.59/1.48  --res_ordering                          kbo
% 7.59/1.48  --res_to_prop_solver                    active
% 7.59/1.48  --res_prop_simpl_new                    false
% 7.59/1.48  --res_prop_simpl_given                  true
% 7.59/1.48  --res_passive_queue_type                priority_queues
% 7.59/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.48  --res_passive_queues_freq               [15;5]
% 7.59/1.48  --res_forward_subs                      full
% 7.59/1.48  --res_backward_subs                     full
% 7.59/1.48  --res_forward_subs_resolution           true
% 7.59/1.48  --res_backward_subs_resolution          true
% 7.59/1.48  --res_orphan_elimination                true
% 7.59/1.48  --res_time_limit                        2.
% 7.59/1.48  --res_out_proof                         true
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Options
% 7.59/1.48  
% 7.59/1.48  --superposition_flag                    true
% 7.59/1.48  --sup_passive_queue_type                priority_queues
% 7.59/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.48  --demod_completeness_check              fast
% 7.59/1.48  --demod_use_ground                      true
% 7.59/1.48  --sup_to_prop_solver                    passive
% 7.59/1.48  --sup_prop_simpl_new                    true
% 7.59/1.48  --sup_prop_simpl_given                  true
% 7.59/1.48  --sup_fun_splitting                     true
% 7.59/1.48  --sup_smt_interval                      50000
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Simplification Setup
% 7.59/1.48  
% 7.59/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.48  --sup_immed_triv                        [TrivRules]
% 7.59/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_immed_bw_main                     []
% 7.59/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_input_bw                          []
% 7.59/1.48  
% 7.59/1.48  ------ Combination Options
% 7.59/1.48  
% 7.59/1.48  --comb_res_mult                         3
% 7.59/1.48  --comb_sup_mult                         2
% 7.59/1.48  --comb_inst_mult                        10
% 7.59/1.48  
% 7.59/1.48  ------ Debug Options
% 7.59/1.48  
% 7.59/1.48  --dbg_backtrace                         false
% 7.59/1.48  --dbg_dump_prop_clauses                 false
% 7.59/1.48  --dbg_dump_prop_clauses_file            -
% 7.59/1.48  --dbg_out_stat                          false
% 7.59/1.48  ------ Parsing...
% 7.59/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.48  ------ Proving...
% 7.59/1.48  ------ Problem Properties 
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  clauses                                 31
% 7.59/1.48  conjectures                             17
% 7.59/1.48  EPR                                     16
% 7.59/1.48  Horn                                    27
% 7.59/1.48  unary                                   17
% 7.59/1.48  binary                                  2
% 7.59/1.48  lits                                    102
% 7.59/1.48  lits eq                                 8
% 7.59/1.48  fd_pure                                 0
% 7.59/1.48  fd_pseudo                               0
% 7.59/1.48  fd_cond                                 0
% 7.59/1.48  fd_pseudo_cond                          0
% 7.59/1.48  AC symbols                              0
% 7.59/1.48  
% 7.59/1.48  ------ Schedule dynamic 5 is on 
% 7.59/1.48  
% 7.59/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  ------ 
% 7.59/1.48  Current options:
% 7.59/1.48  ------ 
% 7.59/1.48  
% 7.59/1.48  ------ Input Options
% 7.59/1.48  
% 7.59/1.48  --out_options                           all
% 7.59/1.48  --tptp_safe_out                         true
% 7.59/1.48  --problem_path                          ""
% 7.59/1.48  --include_path                          ""
% 7.59/1.48  --clausifier                            res/vclausify_rel
% 7.59/1.48  --clausifier_options                    ""
% 7.59/1.48  --stdin                                 false
% 7.59/1.48  --stats_out                             all
% 7.59/1.48  
% 7.59/1.48  ------ General Options
% 7.59/1.48  
% 7.59/1.48  --fof                                   false
% 7.59/1.48  --time_out_real                         305.
% 7.59/1.48  --time_out_virtual                      -1.
% 7.59/1.48  --symbol_type_check                     false
% 7.59/1.48  --clausify_out                          false
% 7.59/1.48  --sig_cnt_out                           false
% 7.59/1.48  --trig_cnt_out                          false
% 7.59/1.48  --trig_cnt_out_tolerance                1.
% 7.59/1.48  --trig_cnt_out_sk_spl                   false
% 7.59/1.48  --abstr_cl_out                          false
% 7.59/1.48  
% 7.59/1.48  ------ Global Options
% 7.59/1.48  
% 7.59/1.48  --schedule                              default
% 7.59/1.48  --add_important_lit                     false
% 7.59/1.48  --prop_solver_per_cl                    1000
% 7.59/1.48  --min_unsat_core                        false
% 7.59/1.48  --soft_assumptions                      false
% 7.59/1.48  --soft_lemma_size                       3
% 7.59/1.48  --prop_impl_unit_size                   0
% 7.59/1.48  --prop_impl_unit                        []
% 7.59/1.48  --share_sel_clauses                     true
% 7.59/1.48  --reset_solvers                         false
% 7.59/1.48  --bc_imp_inh                            [conj_cone]
% 7.59/1.48  --conj_cone_tolerance                   3.
% 7.59/1.48  --extra_neg_conj                        none
% 7.59/1.48  --large_theory_mode                     true
% 7.59/1.48  --prolific_symb_bound                   200
% 7.59/1.48  --lt_threshold                          2000
% 7.59/1.48  --clause_weak_htbl                      true
% 7.59/1.48  --gc_record_bc_elim                     false
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing Options
% 7.59/1.48  
% 7.59/1.48  --preprocessing_flag                    true
% 7.59/1.48  --time_out_prep_mult                    0.1
% 7.59/1.48  --splitting_mode                        input
% 7.59/1.48  --splitting_grd                         true
% 7.59/1.48  --splitting_cvd                         false
% 7.59/1.48  --splitting_cvd_svl                     false
% 7.59/1.48  --splitting_nvd                         32
% 7.59/1.48  --sub_typing                            true
% 7.59/1.48  --prep_gs_sim                           true
% 7.59/1.48  --prep_unflatten                        true
% 7.59/1.48  --prep_res_sim                          true
% 7.59/1.48  --prep_upred                            true
% 7.59/1.48  --prep_sem_filter                       exhaustive
% 7.59/1.48  --prep_sem_filter_out                   false
% 7.59/1.48  --pred_elim                             true
% 7.59/1.48  --res_sim_input                         true
% 7.59/1.48  --eq_ax_congr_red                       true
% 7.59/1.48  --pure_diseq_elim                       true
% 7.59/1.48  --brand_transform                       false
% 7.59/1.48  --non_eq_to_eq                          false
% 7.59/1.48  --prep_def_merge                        true
% 7.59/1.48  --prep_def_merge_prop_impl              false
% 7.59/1.48  --prep_def_merge_mbd                    true
% 7.59/1.48  --prep_def_merge_tr_red                 false
% 7.59/1.48  --prep_def_merge_tr_cl                  false
% 7.59/1.48  --smt_preprocessing                     true
% 7.59/1.48  --smt_ac_axioms                         fast
% 7.59/1.48  --preprocessed_out                      false
% 7.59/1.48  --preprocessed_stats                    false
% 7.59/1.48  
% 7.59/1.48  ------ Abstraction refinement Options
% 7.59/1.48  
% 7.59/1.48  --abstr_ref                             []
% 7.59/1.48  --abstr_ref_prep                        false
% 7.59/1.48  --abstr_ref_until_sat                   false
% 7.59/1.48  --abstr_ref_sig_restrict                funpre
% 7.59/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.48  --abstr_ref_under                       []
% 7.59/1.48  
% 7.59/1.48  ------ SAT Options
% 7.59/1.48  
% 7.59/1.48  --sat_mode                              false
% 7.59/1.48  --sat_fm_restart_options                ""
% 7.59/1.48  --sat_gr_def                            false
% 7.59/1.48  --sat_epr_types                         true
% 7.59/1.48  --sat_non_cyclic_types                  false
% 7.59/1.48  --sat_finite_models                     false
% 7.59/1.48  --sat_fm_lemmas                         false
% 7.59/1.48  --sat_fm_prep                           false
% 7.59/1.48  --sat_fm_uc_incr                        true
% 7.59/1.48  --sat_out_model                         small
% 7.59/1.48  --sat_out_clauses                       false
% 7.59/1.48  
% 7.59/1.48  ------ QBF Options
% 7.59/1.48  
% 7.59/1.48  --qbf_mode                              false
% 7.59/1.48  --qbf_elim_univ                         false
% 7.59/1.48  --qbf_dom_inst                          none
% 7.59/1.48  --qbf_dom_pre_inst                      false
% 7.59/1.48  --qbf_sk_in                             false
% 7.59/1.48  --qbf_pred_elim                         true
% 7.59/1.48  --qbf_split                             512
% 7.59/1.48  
% 7.59/1.48  ------ BMC1 Options
% 7.59/1.48  
% 7.59/1.48  --bmc1_incremental                      false
% 7.59/1.48  --bmc1_axioms                           reachable_all
% 7.59/1.48  --bmc1_min_bound                        0
% 7.59/1.48  --bmc1_max_bound                        -1
% 7.59/1.48  --bmc1_max_bound_default                -1
% 7.59/1.48  --bmc1_symbol_reachability              true
% 7.59/1.48  --bmc1_property_lemmas                  false
% 7.59/1.48  --bmc1_k_induction                      false
% 7.59/1.48  --bmc1_non_equiv_states                 false
% 7.59/1.48  --bmc1_deadlock                         false
% 7.59/1.48  --bmc1_ucm                              false
% 7.59/1.48  --bmc1_add_unsat_core                   none
% 7.59/1.48  --bmc1_unsat_core_children              false
% 7.59/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.48  --bmc1_out_stat                         full
% 7.59/1.48  --bmc1_ground_init                      false
% 7.59/1.48  --bmc1_pre_inst_next_state              false
% 7.59/1.48  --bmc1_pre_inst_state                   false
% 7.59/1.48  --bmc1_pre_inst_reach_state             false
% 7.59/1.48  --bmc1_out_unsat_core                   false
% 7.59/1.48  --bmc1_aig_witness_out                  false
% 7.59/1.48  --bmc1_verbose                          false
% 7.59/1.48  --bmc1_dump_clauses_tptp                false
% 7.59/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.48  --bmc1_dump_file                        -
% 7.59/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.48  --bmc1_ucm_extend_mode                  1
% 7.59/1.48  --bmc1_ucm_init_mode                    2
% 7.59/1.48  --bmc1_ucm_cone_mode                    none
% 7.59/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.48  --bmc1_ucm_relax_model                  4
% 7.59/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.48  --bmc1_ucm_layered_model                none
% 7.59/1.48  --bmc1_ucm_max_lemma_size               10
% 7.59/1.48  
% 7.59/1.48  ------ AIG Options
% 7.59/1.48  
% 7.59/1.48  --aig_mode                              false
% 7.59/1.48  
% 7.59/1.48  ------ Instantiation Options
% 7.59/1.48  
% 7.59/1.48  --instantiation_flag                    true
% 7.59/1.48  --inst_sos_flag                         true
% 7.59/1.48  --inst_sos_phase                        true
% 7.59/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel_side                     none
% 7.59/1.48  --inst_solver_per_active                1400
% 7.59/1.48  --inst_solver_calls_frac                1.
% 7.59/1.48  --inst_passive_queue_type               priority_queues
% 7.59/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.48  --inst_passive_queues_freq              [25;2]
% 7.59/1.48  --inst_dismatching                      true
% 7.59/1.48  --inst_eager_unprocessed_to_passive     true
% 7.59/1.48  --inst_prop_sim_given                   true
% 7.59/1.48  --inst_prop_sim_new                     false
% 7.59/1.48  --inst_subs_new                         false
% 7.59/1.48  --inst_eq_res_simp                      false
% 7.59/1.48  --inst_subs_given                       false
% 7.59/1.48  --inst_orphan_elimination               true
% 7.59/1.48  --inst_learning_loop_flag               true
% 7.59/1.48  --inst_learning_start                   3000
% 7.59/1.48  --inst_learning_factor                  2
% 7.59/1.48  --inst_start_prop_sim_after_learn       3
% 7.59/1.48  --inst_sel_renew                        solver
% 7.59/1.48  --inst_lit_activity_flag                true
% 7.59/1.48  --inst_restr_to_given                   false
% 7.59/1.48  --inst_activity_threshold               500
% 7.59/1.48  --inst_out_proof                        true
% 7.59/1.48  
% 7.59/1.48  ------ Resolution Options
% 7.59/1.48  
% 7.59/1.48  --resolution_flag                       false
% 7.59/1.48  --res_lit_sel                           adaptive
% 7.59/1.48  --res_lit_sel_side                      none
% 7.59/1.48  --res_ordering                          kbo
% 7.59/1.48  --res_to_prop_solver                    active
% 7.59/1.48  --res_prop_simpl_new                    false
% 7.59/1.48  --res_prop_simpl_given                  true
% 7.59/1.48  --res_passive_queue_type                priority_queues
% 7.59/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.48  --res_passive_queues_freq               [15;5]
% 7.59/1.48  --res_forward_subs                      full
% 7.59/1.48  --res_backward_subs                     full
% 7.59/1.48  --res_forward_subs_resolution           true
% 7.59/1.48  --res_backward_subs_resolution          true
% 7.59/1.48  --res_orphan_elimination                true
% 7.59/1.48  --res_time_limit                        2.
% 7.59/1.48  --res_out_proof                         true
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Options
% 7.59/1.48  
% 7.59/1.48  --superposition_flag                    true
% 7.59/1.48  --sup_passive_queue_type                priority_queues
% 7.59/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.48  --demod_completeness_check              fast
% 7.59/1.48  --demod_use_ground                      true
% 7.59/1.48  --sup_to_prop_solver                    passive
% 7.59/1.48  --sup_prop_simpl_new                    true
% 7.59/1.48  --sup_prop_simpl_given                  true
% 7.59/1.48  --sup_fun_splitting                     true
% 7.59/1.48  --sup_smt_interval                      50000
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Simplification Setup
% 7.59/1.48  
% 7.59/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.59/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.59/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.59/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.59/1.48  --sup_immed_triv                        [TrivRules]
% 7.59/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_immed_bw_main                     []
% 7.59/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.59/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_input_bw                          []
% 7.59/1.48  
% 7.59/1.48  ------ Combination Options
% 7.59/1.48  
% 7.59/1.48  --comb_res_mult                         3
% 7.59/1.48  --comb_sup_mult                         2
% 7.59/1.48  --comb_inst_mult                        10
% 7.59/1.48  
% 7.59/1.48  ------ Debug Options
% 7.59/1.48  
% 7.59/1.48  --dbg_backtrace                         false
% 7.59/1.48  --dbg_dump_prop_clauses                 false
% 7.59/1.48  --dbg_dump_prop_clauses_file            -
% 7.59/1.48  --dbg_out_stat                          false
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  ------ Proving...
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  % SZS status Theorem for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  fof(f6,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f25,plain,(
% 7.59/1.48    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f6])).
% 7.59/1.48  
% 7.59/1.48  fof(f26,plain,(
% 7.59/1.48    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.48    inference(flattening,[],[f25])).
% 7.59/1.48  
% 7.59/1.48  fof(f60,plain,(
% 7.59/1.48    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f26])).
% 7.59/1.48  
% 7.59/1.48  fof(f16,conjecture,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f17,negated_conjecture,(
% 7.59/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.59/1.48    inference(negated_conjecture,[],[f16])).
% 7.59/1.48  
% 7.59/1.48  fof(f42,plain,(
% 7.59/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f17])).
% 7.59/1.48  
% 7.59/1.48  fof(f43,plain,(
% 7.59/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.59/1.48    inference(flattening,[],[f42])).
% 7.59/1.48  
% 7.59/1.48  fof(f53,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f52,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f51,plain,(
% 7.59/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f50,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f49,plain,(
% 7.59/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f48,plain,(
% 7.59/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f47,plain,(
% 7.59/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f54,plain,(
% 7.59/1.48    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.59/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f53,f52,f51,f50,f49,f48,f47])).
% 7.59/1.48  
% 7.59/1.48  fof(f80,plain,(
% 7.59/1.48    m1_pre_topc(sK2,sK0)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f12,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f35,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f12])).
% 7.59/1.48  
% 7.59/1.48  fof(f36,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.48    inference(flattening,[],[f35])).
% 7.59/1.48  
% 7.59/1.48  fof(f68,plain,(
% 7.59/1.48    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f36])).
% 7.59/1.48  
% 7.59/1.48  fof(f86,plain,(
% 7.59/1.48    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f73,plain,(
% 7.59/1.48    ~v2_struct_0(sK0)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f74,plain,(
% 7.59/1.48    v2_pre_topc(sK0)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f75,plain,(
% 7.59/1.48    l1_pre_topc(sK0)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f79,plain,(
% 7.59/1.48    ~v2_struct_0(sK2)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f11,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f33,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f11])).
% 7.59/1.48  
% 7.59/1.48  fof(f34,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.48    inference(flattening,[],[f33])).
% 7.59/1.48  
% 7.59/1.48  fof(f67,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f34])).
% 7.59/1.48  
% 7.59/1.48  fof(f8,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f18,plain,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 7.59/1.48    inference(pure_predicate_removal,[],[f8])).
% 7.59/1.48  
% 7.59/1.48  fof(f29,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f18])).
% 7.59/1.48  
% 7.59/1.48  fof(f62,plain,(
% 7.59/1.48    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f29])).
% 7.59/1.48  
% 7.59/1.48  fof(f4,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f23,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f4])).
% 7.59/1.48  
% 7.59/1.48  fof(f58,plain,(
% 7.59/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f23])).
% 7.59/1.48  
% 7.59/1.48  fof(f3,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f22,plain,(
% 7.59/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f3])).
% 7.59/1.48  
% 7.59/1.48  fof(f57,plain,(
% 7.59/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f22])).
% 7.59/1.48  
% 7.59/1.48  fof(f2,axiom,(
% 7.59/1.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f21,plain,(
% 7.59/1.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f2])).
% 7.59/1.48  
% 7.59/1.48  fof(f56,plain,(
% 7.59/1.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f21])).
% 7.59/1.48  
% 7.59/1.48  fof(f10,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f32,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f10])).
% 7.59/1.48  
% 7.59/1.48  fof(f66,plain,(
% 7.59/1.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f32])).
% 7.59/1.48  
% 7.59/1.48  fof(f5,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f24,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f5])).
% 7.59/1.48  
% 7.59/1.48  fof(f59,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f24])).
% 7.59/1.48  
% 7.59/1.48  fof(f82,plain,(
% 7.59/1.48    m1_pre_topc(sK3,sK0)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f7,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f27,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f7])).
% 7.59/1.48  
% 7.59/1.48  fof(f28,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(flattening,[],[f27])).
% 7.59/1.48  
% 7.59/1.48  fof(f61,plain,(
% 7.59/1.48    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f28])).
% 7.59/1.48  
% 7.59/1.48  fof(f92,plain,(
% 7.59/1.48    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(equality_resolution,[],[f61])).
% 7.59/1.48  
% 7.59/1.48  fof(f90,plain,(
% 7.59/1.48    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f89,plain,(
% 7.59/1.48    sK5 = sK6),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f9,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f30,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f9])).
% 7.59/1.48  
% 7.59/1.48  fof(f31,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.48    inference(flattening,[],[f30])).
% 7.59/1.48  
% 7.59/1.48  fof(f44,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.48    inference(nnf_transformation,[],[f31])).
% 7.59/1.48  
% 7.59/1.48  fof(f45,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.48    inference(flattening,[],[f44])).
% 7.59/1.48  
% 7.59/1.48  fof(f64,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f45])).
% 7.59/1.48  
% 7.59/1.48  fof(f94,plain,(
% 7.59/1.48    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.48    inference(equality_resolution,[],[f64])).
% 7.59/1.48  
% 7.59/1.48  fof(f15,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f40,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f15])).
% 7.59/1.48  
% 7.59/1.48  fof(f41,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.48    inference(flattening,[],[f40])).
% 7.59/1.48  
% 7.59/1.48  fof(f46,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.48    inference(nnf_transformation,[],[f41])).
% 7.59/1.48  
% 7.59/1.48  fof(f72,plain,(
% 7.59/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f46])).
% 7.59/1.48  
% 7.59/1.48  fof(f96,plain,(
% 7.59/1.48    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.48    inference(equality_resolution,[],[f72])).
% 7.59/1.48  
% 7.59/1.48  fof(f84,plain,(
% 7.59/1.48    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f83,plain,(
% 7.59/1.48    v1_funct_1(sK4)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f14,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f38,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f14])).
% 7.59/1.48  
% 7.59/1.48  fof(f39,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.48    inference(flattening,[],[f38])).
% 7.59/1.48  
% 7.59/1.48  fof(f70,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f39])).
% 7.59/1.48  
% 7.59/1.48  fof(f1,axiom,(
% 7.59/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f19,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.48    inference(ennf_transformation,[],[f1])).
% 7.59/1.48  
% 7.59/1.48  fof(f20,plain,(
% 7.59/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.48    inference(flattening,[],[f19])).
% 7.59/1.48  
% 7.59/1.48  fof(f55,plain,(
% 7.59/1.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f20])).
% 7.59/1.48  
% 7.59/1.48  fof(f76,plain,(
% 7.59/1.48    ~v2_struct_0(sK1)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f77,plain,(
% 7.59/1.48    v2_pre_topc(sK1)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f78,plain,(
% 7.59/1.48    l1_pre_topc(sK1)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f81,plain,(
% 7.59/1.48    ~v2_struct_0(sK3)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f85,plain,(
% 7.59/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f87,plain,(
% 7.59/1.48    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f91,plain,(
% 7.59/1.48    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f88,plain,(
% 7.59/1.48    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.59/1.48    inference(cnf_transformation,[],[f54])).
% 7.59/1.48  
% 7.59/1.48  fof(f13,axiom,(
% 7.59/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.59/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f37,plain,(
% 7.59/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f13])).
% 7.59/1.48  
% 7.59/1.48  fof(f69,plain,(
% 7.59/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f37])).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5,plain,
% 7.59/1.48      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.59/1.48      | ~ l1_pre_topc(X0)
% 7.59/1.48      | ~ v2_pre_topc(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_875,plain,
% 7.59/1.48      ( v3_pre_topc(k2_struct_0(X0_54),X0_54)
% 7.59/1.48      | ~ l1_pre_topc(X0_54)
% 7.59/1.48      | ~ v2_pre_topc(X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1408,plain,
% 7.59/1.48      ( v3_pre_topc(k2_struct_0(X0_54),X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_29,negated_conjecture,
% 7.59/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_858,negated_conjecture,
% 7.59/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_29]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1423,plain,
% 7.59/1.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_13,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_870,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | v2_struct_0(X1_54)
% 7.59/1.48      | v2_struct_0(X0_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54)
% 7.59/1.48      | ~ v2_pre_topc(X1_54)
% 7.59/1.48      | g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_13]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1413,plain,
% 7.59/1.48      ( g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)) = k1_tsep_1(X1_54,X0_54,X0_54)
% 7.59/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_870]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2812,plain,
% 7.59/1.48      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 7.59/1.48      | v2_struct_0(sK0) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1423,c_1413]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_23,negated_conjecture,
% 7.59/1.48      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.59/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_862,negated_conjecture,
% 7.59/1.48      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2816,plain,
% 7.59/1.48      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 7.59/1.48      | v2_struct_0(sK0) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.59/1.48      inference(light_normalisation,[status(thm)],[c_2812,c_862]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_36,negated_conjecture,
% 7.59/1.48      ( ~ v2_struct_0(sK0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_37,plain,
% 7.59/1.48      ( v2_struct_0(sK0) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_35,negated_conjecture,
% 7.59/1.48      ( v2_pre_topc(sK0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_38,plain,
% 7.59/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_34,negated_conjecture,
% 7.59/1.48      ( l1_pre_topc(sK0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_39,plain,
% 7.59/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_30,negated_conjecture,
% 7.59/1.48      ( ~ v2_struct_0(sK2) ),
% 7.59/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_43,plain,
% 7.59/1.48      ( v2_struct_0(sK2) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2827,plain,
% 7.59/1.48      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2816,c_37,c_38,c_39,c_43]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ m1_pre_topc(X2,X1)
% 7.59/1.48      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_871,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | ~ m1_pre_topc(X2_54,X1_54)
% 7.59/1.48      | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54))
% 7.59/1.48      | v2_struct_0(X1_54)
% 7.59/1.48      | v2_struct_0(X0_54)
% 7.59/1.48      | v2_struct_0(X2_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54)
% 7.59/1.48      | ~ v2_pre_topc(X1_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_12]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1412,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,k1_tsep_1(X1_54,X0_54,X2_54)) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.59/1.48      | ~ l1_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_873,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1410,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_54),u1_pre_topc(X0_54)),X1_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2321,plain,
% 7.59/1.48      ( m1_pre_topc(sK2,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_862,c_1410]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3387,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,k1_tsep_1(X1_54,sK2,X0_54)) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(k1_tsep_1(X1_54,sK2,X0_54)) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1412,c_2321]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3751,plain,
% 7.59/1.48      ( v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,k1_tsep_1(X1_54,sK2,X0_54)) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(k1_tsep_1(X1_54,sK2,X0_54)) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_3387,c_43]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3752,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,k1_tsep_1(X1_54,sK2,X0_54)) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(k1_tsep_1(X1_54,sK2,X0_54)) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_3751]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_877,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54)
% 7.59/1.48      | l1_pre_topc(X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1406,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2140,plain,
% 7.59/1.48      ( l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK2) = iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1423,c_1406]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2501,plain,
% 7.59/1.48      ( l1_pre_topc(sK2) = iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2140,c_39]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2,plain,
% 7.59/1.48      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1,plain,
% 7.59/1.48      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_369,plain,
% 7.59/1.48      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_850,plain,
% 7.59/1.48      ( ~ l1_pre_topc(X0_54) | u1_struct_0(X0_54) = k2_struct_0(X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_369]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1431,plain,
% 7.59/1.48      ( u1_struct_0(X0_54) = k2_struct_0(X0_54)
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3400,plain,
% 7.59/1.48      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2501,c_1431]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_11,plain,
% 7.59/1.48      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.48      | ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_872,plain,
% 7.59/1.48      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54)))
% 7.59/1.48      | ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1411,plain,
% 7.59/1.48      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3922,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3400,c_1411]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.59/1.48      | ~ m1_pre_topc(X1,X2)
% 7.59/1.48      | ~ l1_pre_topc(X2) ),
% 7.59/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_876,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
% 7.59/1.48      | ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1407,plain,
% 7.59/1.48      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5308,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3922,c_1407]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12743,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK2,X1_54)))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(k1_tsep_1(X0_54,sK2,X1_54)) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.59/1.48      | v2_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3752,c_5308]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_44,plain,
% 7.59/1.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_27,negated_conjecture,
% 7.59/1.48      ( m1_pre_topc(sK3,sK0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_46,plain,
% 7.59/1.48      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1748,plain,
% 7.59/1.48      ( ~ m1_pre_topc(sK3,X0_54)
% 7.59/1.48      | ~ l1_pre_topc(X0_54)
% 7.59/1.48      | l1_pre_topc(sK3) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_877]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1980,plain,
% 7.59/1.48      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_1748]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1981,plain,
% 7.59/1.48      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK3) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3382,plain,
% 7.59/1.48      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK3) = iProver_top
% 7.59/1.48      | v2_struct_0(sK0) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2827,c_1412]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_16316,plain,
% 7.59/1.48      ( l1_pre_topc(k1_tsep_1(X0_54,sK2,X1_54)) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK2,X1_54)))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_12743,c_37,c_38,c_39,c_43,c_44,c_46,c_1981,c_3382]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_16317,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,sK2,X1_54)))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,X0_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(k1_tsep_1(X0_54,sK2,X1_54)) != iProver_top
% 7.59/1.48      | v2_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_16316]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_16322,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.59/1.48      | v2_struct_0(sK0) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2827,c_16317]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_860,negated_conjecture,
% 7.59/1.48      ( m1_pre_topc(sK3,sK0) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_27]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1421,plain,
% 7.59/1.48      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2139,plain,
% 7.59/1.48      ( l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK3) = iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1421,c_1406]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2429,plain,
% 7.59/1.48      ( l1_pre_topc(sK3) = iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2139,c_39,c_46,c_1981]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3399,plain,
% 7.59/1.48      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2429,c_1431]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_16329,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.59/1.48      | v2_struct_0(sK0) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.59/1.48      inference(light_normalisation,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_16322,c_2827,c_3399]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3826,plain,
% 7.59/1.48      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK3) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3399,c_1411]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5288,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_3826,c_39,c_46,c_1981]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5289,plain,
% 7.59/1.48      ( m1_subset_1(u1_struct_0(X0_54),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_5288]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5294,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3400,c_5289]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_16386,plain,
% 7.59/1.48      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_16329,c_37,c_38,c_39,c_43,c_44,c_3382,c_5294]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_6,plain,
% 7.59/1.48      ( ~ v3_pre_topc(X0,X1)
% 7.59/1.48      | v3_pre_topc(X0,X2)
% 7.59/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.59/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.48      | ~ m1_pre_topc(X2,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_874,plain,
% 7.59/1.48      ( ~ v3_pre_topc(X0_55,X0_54)
% 7.59/1.48      | v3_pre_topc(X0_55,X1_54)
% 7.59/1.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54)))
% 7.59/1.48      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54)))
% 7.59/1.48      | ~ m1_pre_topc(X1_54,X0_54)
% 7.59/1.48      | ~ l1_pre_topc(X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1409,plain,
% 7.59/1.48      ( v3_pre_topc(X0_55,X0_54) != iProver_top
% 7.59/1.48      | v3_pre_topc(X0_55,X1_54) = iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X1_54))) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3825,plain,
% 7.59/1.48      ( v3_pre_topc(X0_55,X0_54) != iProver_top
% 7.59/1.48      | v3_pre_topc(X0_55,sK3) = iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3399,c_1409]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3822,plain,
% 7.59/1.48      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_54))) = iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3399,c_1407]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_20587,plain,
% 7.59/1.48      ( v3_pre_topc(X0_55,sK3) = iProver_top
% 7.59/1.48      | v3_pre_topc(X0_55,X0_54) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_3825,c_3822]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_20588,plain,
% 7.59/1.48      ( v3_pre_topc(X0_55,X0_54) != iProver_top
% 7.59/1.48      | v3_pre_topc(X0_55,sK3) = iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_20587]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_20597,plain,
% 7.59/1.48      ( v3_pre_topc(k2_struct_0(sK2),X0_54) != iProver_top
% 7.59/1.48      | v3_pre_topc(k2_struct_0(sK2),sK3) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_16386,c_20588]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_19,negated_conjecture,
% 7.59/1.48      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.59/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_866,negated_conjecture,
% 7.59/1.48      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_19]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1417,plain,
% 7.59/1.48      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_866]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_20,negated_conjecture,
% 7.59/1.48      ( sK5 = sK6 ),
% 7.59/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_865,negated_conjecture,
% 7.59/1.48      ( sK5 = sK6 ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_20]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1435,plain,
% 7.59/1.48      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.59/1.48      inference(light_normalisation,[status(thm)],[c_1417,c_865]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_9,plain,
% 7.59/1.48      ( v1_tsep_1(X0,X1)
% 7.59/1.48      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.59/1.48      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.48      | ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_198,plain,
% 7.59/1.48      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.59/1.48      | v1_tsep_1(X0,X1)
% 7.59/1.48      | ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_9,c_11]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_199,plain,
% 7.59/1.48      ( v1_tsep_1(X0,X1)
% 7.59/1.48      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.59/1.48      | ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1) ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_198]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_16,plain,
% 7.59/1.48      ( r1_tmap_1(X0,X1,X2,X3)
% 7.59/1.48      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.59/1.48      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.59/1.48      | ~ v1_tsep_1(X4,X0)
% 7.59/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.59/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_pre_topc(X4,X5)
% 7.59/1.48      | ~ m1_pre_topc(X4,X0)
% 7.59/1.48      | ~ m1_pre_topc(X0,X5)
% 7.59/1.48      | ~ v1_funct_1(X2)
% 7.59/1.48      | v2_struct_0(X5)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X4)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | ~ l1_pre_topc(X5)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X5)
% 7.59/1.48      | ~ v2_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_25,negated_conjecture,
% 7.59/1.48      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_452,plain,
% 7.59/1.48      ( r1_tmap_1(X0,X1,X2,X3)
% 7.59/1.48      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.59/1.48      | ~ v1_tsep_1(X4,X0)
% 7.59/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.59/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_pre_topc(X4,X5)
% 7.59/1.48      | ~ m1_pre_topc(X4,X0)
% 7.59/1.48      | ~ m1_pre_topc(X0,X5)
% 7.59/1.48      | ~ v1_funct_1(X2)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X5)
% 7.59/1.48      | v2_struct_0(X4)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X5)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X5)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.59/1.48      | sK4 != X2 ),
% 7.59/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_453,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ v1_tsep_1(X0,X3)
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_pre_topc(X0,X2)
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | ~ v1_funct_1(sK4)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(unflattening,[status(thm)],[c_452]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_26,negated_conjecture,
% 7.59/1.48      ( v1_funct_1(sK4) ),
% 7.59/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_457,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X0,X2)
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ v1_tsep_1(X0,X3)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_453,c_26]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_458,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ v1_tsep_1(X0,X3)
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_pre_topc(X0,X2)
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_457]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_15,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ m1_pre_topc(X2,X0)
% 7.59/1.48      | m1_pre_topc(X2,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_501,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ v1_tsep_1(X0,X3)
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(forward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_458,c_15]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_524,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ v3_pre_topc(u1_struct_0(X5),X6)
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_pre_topc(X5,X6)
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | ~ l1_pre_topc(X6)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X6)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | X0 != X5
% 7.59/1.48      | X3 != X6
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(resolution_lifted,[status(thm)],[c_199,c_501]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_525,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ l1_pre_topc(X3)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X3)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(unflattening,[status(thm)],[c_524]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_0,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | v2_pre_topc(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_569,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 7.59/1.48      | r1_tmap_1(X3,X1,sK4,X4)
% 7.59/1.48      | ~ v3_pre_topc(u1_struct_0(X0),X3)
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 7.59/1.48      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 7.59/1.48      | ~ m1_pre_topc(X0,X3)
% 7.59/1.48      | ~ m1_pre_topc(X3,X2)
% 7.59/1.48      | v2_struct_0(X1)
% 7.59/1.48      | v2_struct_0(X0)
% 7.59/1.48      | v2_struct_0(X2)
% 7.59/1.48      | v2_struct_0(X3)
% 7.59/1.48      | ~ l1_pre_topc(X1)
% 7.59/1.48      | ~ l1_pre_topc(X2)
% 7.59/1.48      | ~ v2_pre_topc(X1)
% 7.59/1.48      | ~ v2_pre_topc(X2)
% 7.59/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(forward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_525,c_0,c_3]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_849,plain,
% 7.59/1.48      ( ~ r1_tmap_1(X0_54,X1_54,k3_tmap_1(X2_54,X1_54,X3_54,X0_54,sK4),X0_55)
% 7.59/1.48      | r1_tmap_1(X3_54,X1_54,sK4,X0_55)
% 7.59/1.48      | ~ v3_pre_topc(u1_struct_0(X0_54),X3_54)
% 7.59/1.48      | ~ m1_subset_1(X0_55,u1_struct_0(X0_54))
% 7.59/1.48      | ~ m1_subset_1(X0_55,u1_struct_0(X3_54))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_54),u1_struct_0(X1_54))))
% 7.59/1.48      | ~ m1_pre_topc(X0_54,X3_54)
% 7.59/1.48      | ~ m1_pre_topc(X3_54,X2_54)
% 7.59/1.48      | v2_struct_0(X1_54)
% 7.59/1.48      | v2_struct_0(X0_54)
% 7.59/1.48      | v2_struct_0(X2_54)
% 7.59/1.48      | v2_struct_0(X3_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54)
% 7.59/1.48      | ~ l1_pre_topc(X2_54)
% 7.59/1.48      | ~ v2_pre_topc(X1_54)
% 7.59/1.48      | ~ v2_pre_topc(X2_54)
% 7.59/1.48      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X3_54) != u1_struct_0(sK3) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_569]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1432,plain,
% 7.59/1.48      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 7.59/1.48      | u1_struct_0(X1_54) != u1_struct_0(sK3)
% 7.59/1.48      | r1_tmap_1(X2_54,X0_54,k3_tmap_1(X3_54,X0_54,X1_54,X2_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | r1_tmap_1(X1_54,X0_54,sK4,X0_55) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X2_54),X1_54) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X2_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(X0_54)))) != iProver_top
% 7.59/1.48      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X3_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X3_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X0_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X3_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2134,plain,
% 7.59/1.48      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.59/1.48      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.59/1.48      | v2_struct_0(sK1) = iProver_top
% 7.59/1.48      | l1_pre_topc(X2_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.59/1.48      | v2_pre_topc(X2_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK1) != iProver_top ),
% 7.59/1.48      inference(equality_resolution,[status(thm)],[c_1432]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_33,negated_conjecture,
% 7.59/1.48      ( ~ v2_struct_0(sK1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_40,plain,
% 7.59/1.48      ( v2_struct_0(sK1) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_32,negated_conjecture,
% 7.59/1.48      ( v2_pre_topc(sK1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_41,plain,
% 7.59/1.48      ( v2_pre_topc(sK1) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_31,negated_conjecture,
% 7.59/1.48      ( l1_pre_topc(sK1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_42,plain,
% 7.59/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2582,plain,
% 7.59/1.48      ( v2_pre_topc(X2_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 7.59/1.48      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.59/1.48      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.59/1.48      | l1_pre_topc(X2_54) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2134,c_40,c_41,c_42]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2583,plain,
% 7.59/1.48      ( u1_struct_0(X0_54) != u1_struct_0(sK3)
% 7.59/1.48      | r1_tmap_1(X1_54,sK1,k3_tmap_1(X2_54,sK1,X0_54,X1_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | r1_tmap_1(X0_54,sK1,sK4,X0_55) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X1_54),X0_54) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X1_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1)))) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,X2_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X2_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X2_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X2_54) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_2582]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2586,plain,
% 7.59/1.48      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(sK3) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(equality_resolution,[status(thm)],[c_2583]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28,negated_conjecture,
% 7.59/1.48      ( ~ v2_struct_0(sK3) ),
% 7.59/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_45,plain,
% 7.59/1.48      ( v2_struct_0(sK3) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_24,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_49,plain,
% 7.59/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2668,plain,
% 7.59/1.48      ( v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.59/1.48      | r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2586,c_45,c_49]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2669,plain,
% 7.59/1.48      ( r1_tmap_1(X0_54,sK1,k3_tmap_1(X1_54,sK1,sK3,X0_54,sK4),X0_55) != iProver_top
% 7.59/1.48      | r1_tmap_1(sK3,sK1,sK4,X0_55) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(X0_54),sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(X0_54)) != iProver_top
% 7.59/1.48      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 7.59/1.48      | m1_pre_topc(X0_54,sK3) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X1_54) != iProver_top
% 7.59/1.48      | v2_struct_0(X1_54) = iProver_top
% 7.59/1.48      | v2_struct_0(X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_2668]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2674,plain,
% 7.59/1.48      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.59/1.48      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.59/1.48      | v2_struct_0(sK0) = iProver_top
% 7.59/1.48      | v2_struct_0(sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1435,c_2669]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_22,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_50,plain,
% 7.59/1.48      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_18,negated_conjecture,
% 7.59/1.48      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.59/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_53,plain,
% 7.59/1.48      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_21,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_864,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_21]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1418,plain,
% 7.59/1.48      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1434,plain,
% 7.59/1.48      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.59/1.48      inference(light_normalisation,[status(thm)],[c_1418,c_865]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3143,plain,
% 7.59/1.48      ( m1_pre_topc(sK2,sK3) != iProver_top
% 7.59/1.48      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2674,c_37,c_38,c_39,c_43,c_46,c_50,c_53,c_1434]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3144,plain,
% 7.59/1.48      ( v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_3143]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3914,plain,
% 7.59/1.48      ( v3_pre_topc(k2_struct_0(sK2),sK3) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 7.59/1.48      inference(demodulation,[status(thm)],[c_3400,c_3144]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_21221,plain,
% 7.59/1.48      ( v3_pre_topc(k2_struct_0(sK2),X0_54) != iProver_top
% 7.59/1.48      | m1_pre_topc(sK3,X0_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_20597,c_37,c_38,c_39,c_43,c_44,c_3382,c_3914]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_21227,plain,
% 7.59/1.48      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.59/1.48      | l1_pre_topc(sK2) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK2) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1408,c_21221]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_14,plain,
% 7.59/1.48      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_869,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X0_54) | ~ l1_pre_topc(X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_14]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1414,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X0_54) = iProver_top
% 7.59/1.48      | l1_pre_topc(X0_54) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2426,plain,
% 7.59/1.48      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.59/1.48      | l1_pre_topc(sK2) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1414,c_2321]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_878,plain,
% 7.59/1.48      ( ~ m1_pre_topc(X0_54,X1_54)
% 7.59/1.48      | ~ l1_pre_topc(X1_54)
% 7.59/1.48      | ~ v2_pre_topc(X1_54)
% 7.59/1.48      | v2_pre_topc(X0_54) ),
% 7.59/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1405,plain,
% 7.59/1.48      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 7.59/1.48      | l1_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X1_54) != iProver_top
% 7.59/1.48      | v2_pre_topc(X0_54) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1701,plain,
% 7.59/1.48      ( l1_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.59/1.48      | v2_pre_topc(sK2) = iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_1423,c_1405]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(contradiction,plain,
% 7.59/1.48      ( $false ),
% 7.59/1.48      inference(minisat,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_21227,c_2426,c_2140,c_1701,c_39,c_38]) ).
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  ------                               Statistics
% 7.59/1.48  
% 7.59/1.48  ------ General
% 7.59/1.48  
% 7.59/1.48  abstr_ref_over_cycles:                  0
% 7.59/1.48  abstr_ref_under_cycles:                 0
% 7.59/1.48  gc_basic_clause_elim:                   0
% 7.59/1.48  forced_gc_time:                         0
% 7.59/1.48  parsing_time:                           0.01
% 7.59/1.48  unif_index_cands_time:                  0.
% 7.59/1.48  unif_index_add_time:                    0.
% 7.59/1.48  orderings_time:                         0.
% 7.59/1.48  out_proof_time:                         0.025
% 7.59/1.48  total_time:                             0.886
% 7.59/1.48  num_of_symbols:                         60
% 7.59/1.48  num_of_terms:                           14240
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing
% 7.59/1.48  
% 7.59/1.48  num_of_splits:                          0
% 7.59/1.48  num_of_split_atoms:                     0
% 7.59/1.48  num_of_reused_defs:                     0
% 7.59/1.48  num_eq_ax_congr_red:                    18
% 7.59/1.48  num_of_sem_filtered_clauses:            1
% 7.59/1.48  num_of_subtypes:                        3
% 7.59/1.48  monotx_restored_types:                  0
% 7.59/1.48  sat_num_of_epr_types:                   0
% 7.59/1.48  sat_num_of_non_cyclic_types:            0
% 7.59/1.48  sat_guarded_non_collapsed_types:        0
% 7.59/1.48  num_pure_diseq_elim:                    0
% 7.59/1.48  simp_replaced_by:                       0
% 7.59/1.48  res_preprocessed:                       166
% 7.59/1.48  prep_upred:                             0
% 7.59/1.48  prep_unflattend:                        6
% 7.59/1.48  smt_new_axioms:                         0
% 7.59/1.48  pred_elim_cands:                        7
% 7.59/1.48  pred_elim:                              4
% 7.59/1.48  pred_elim_cl:                           5
% 7.59/1.48  pred_elim_cycles:                       6
% 7.59/1.48  merged_defs:                            0
% 7.59/1.48  merged_defs_ncl:                        0
% 7.59/1.48  bin_hyper_res:                          0
% 7.59/1.48  prep_cycles:                            4
% 7.59/1.48  pred_elim_time:                         0.013
% 7.59/1.48  splitting_time:                         0.
% 7.59/1.48  sem_filter_time:                        0.
% 7.59/1.48  monotx_time:                            0.
% 7.59/1.48  subtype_inf_time:                       0.
% 7.59/1.48  
% 7.59/1.48  ------ Problem properties
% 7.59/1.48  
% 7.59/1.48  clauses:                                31
% 7.59/1.48  conjectures:                            17
% 7.59/1.48  epr:                                    16
% 7.59/1.48  horn:                                   27
% 7.59/1.48  ground:                                 17
% 7.59/1.48  unary:                                  17
% 7.59/1.48  binary:                                 2
% 7.59/1.48  lits:                                   102
% 7.59/1.48  lits_eq:                                8
% 7.59/1.48  fd_pure:                                0
% 7.59/1.48  fd_pseudo:                              0
% 7.59/1.48  fd_cond:                                0
% 7.59/1.48  fd_pseudo_cond:                         0
% 7.59/1.48  ac_symbols:                             0
% 7.59/1.48  
% 7.59/1.48  ------ Propositional Solver
% 7.59/1.48  
% 7.59/1.48  prop_solver_calls:                      34
% 7.59/1.48  prop_fast_solver_calls:                 2868
% 7.59/1.48  smt_solver_calls:                       0
% 7.59/1.48  smt_fast_solver_calls:                  0
% 7.59/1.48  prop_num_of_clauses:                    10384
% 7.59/1.48  prop_preprocess_simplified:             13312
% 7.59/1.48  prop_fo_subsumed:                       282
% 7.59/1.48  prop_solver_time:                       0.
% 7.59/1.48  smt_solver_time:                        0.
% 7.59/1.48  smt_fast_solver_time:                   0.
% 7.59/1.48  prop_fast_solver_time:                  0.
% 7.59/1.48  prop_unsat_core_time:                   0.001
% 7.59/1.48  
% 7.59/1.48  ------ QBF
% 7.59/1.48  
% 7.59/1.48  qbf_q_res:                              0
% 7.59/1.48  qbf_num_tautologies:                    0
% 7.59/1.48  qbf_prep_cycles:                        0
% 7.59/1.48  
% 7.59/1.48  ------ BMC1
% 7.59/1.48  
% 7.59/1.48  bmc1_current_bound:                     -1
% 7.59/1.48  bmc1_last_solved_bound:                 -1
% 7.59/1.48  bmc1_unsat_core_size:                   -1
% 7.59/1.48  bmc1_unsat_core_parents_size:           -1
% 7.59/1.48  bmc1_merge_next_fun:                    0
% 7.59/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.59/1.48  
% 7.59/1.48  ------ Instantiation
% 7.59/1.48  
% 7.59/1.48  inst_num_of_clauses:                    2014
% 7.59/1.48  inst_num_in_passive:                    131
% 7.59/1.48  inst_num_in_active:                     1256
% 7.59/1.48  inst_num_in_unprocessed:                627
% 7.59/1.48  inst_num_of_loops:                      1350
% 7.59/1.48  inst_num_of_learning_restarts:          0
% 7.59/1.48  inst_num_moves_active_passive:          87
% 7.59/1.48  inst_lit_activity:                      0
% 7.59/1.48  inst_lit_activity_moves:                0
% 7.59/1.48  inst_num_tautologies:                   0
% 7.59/1.48  inst_num_prop_implied:                  0
% 7.59/1.48  inst_num_existing_simplified:           0
% 7.59/1.48  inst_num_eq_res_simplified:             0
% 7.59/1.48  inst_num_child_elim:                    0
% 7.59/1.48  inst_num_of_dismatching_blockings:      1279
% 7.59/1.48  inst_num_of_non_proper_insts:           3151
% 7.59/1.48  inst_num_of_duplicates:                 0
% 7.59/1.48  inst_inst_num_from_inst_to_res:         0
% 7.59/1.48  inst_dismatching_checking_time:         0.
% 7.59/1.48  
% 7.59/1.48  ------ Resolution
% 7.59/1.48  
% 7.59/1.48  res_num_of_clauses:                     0
% 7.59/1.48  res_num_in_passive:                     0
% 7.59/1.48  res_num_in_active:                      0
% 7.59/1.48  res_num_of_loops:                       170
% 7.59/1.48  res_forward_subset_subsumed:            249
% 7.59/1.48  res_backward_subset_subsumed:           2
% 7.59/1.48  res_forward_subsumed:                   0
% 7.59/1.48  res_backward_subsumed:                  0
% 7.59/1.48  res_forward_subsumption_resolution:     6
% 7.59/1.48  res_backward_subsumption_resolution:    0
% 7.59/1.48  res_clause_to_clause_subsumption:       5486
% 7.59/1.48  res_orphan_elimination:                 0
% 7.59/1.48  res_tautology_del:                      532
% 7.59/1.48  res_num_eq_res_simplified:              0
% 7.59/1.48  res_num_sel_changes:                    0
% 7.59/1.48  res_moves_from_active_to_pass:          0
% 7.59/1.48  
% 7.59/1.48  ------ Superposition
% 7.59/1.48  
% 7.59/1.48  sup_time_total:                         0.
% 7.59/1.48  sup_time_generating:                    0.
% 7.59/1.48  sup_time_sim_full:                      0.
% 7.59/1.48  sup_time_sim_immed:                     0.
% 7.59/1.48  
% 7.59/1.48  sup_num_of_clauses:                     1047
% 7.59/1.48  sup_num_in_active:                      192
% 7.59/1.48  sup_num_in_passive:                     855
% 7.59/1.48  sup_num_of_loops:                       268
% 7.59/1.48  sup_fw_superposition:                   1191
% 7.59/1.48  sup_bw_superposition:                   768
% 7.59/1.48  sup_immediate_simplified:               1230
% 7.59/1.48  sup_given_eliminated:                   0
% 7.59/1.48  comparisons_done:                       0
% 7.59/1.48  comparisons_avoided:                    0
% 7.59/1.48  
% 7.59/1.48  ------ Simplifications
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  sim_fw_subset_subsumed:                 281
% 7.59/1.48  sim_bw_subset_subsumed:                 105
% 7.59/1.48  sim_fw_subsumed:                        305
% 7.59/1.48  sim_bw_subsumed:                        20
% 7.59/1.48  sim_fw_subsumption_res:                 0
% 7.59/1.48  sim_bw_subsumption_res:                 0
% 7.59/1.48  sim_tautology_del:                      37
% 7.59/1.48  sim_eq_tautology_del:                   8
% 7.59/1.48  sim_eq_res_simp:                        0
% 7.59/1.48  sim_fw_demodulated:                     22
% 7.59/1.48  sim_bw_demodulated:                     77
% 7.59/1.48  sim_light_normalised:                   806
% 7.59/1.48  sim_joinable_taut:                      0
% 7.59/1.48  sim_joinable_simp:                      0
% 7.59/1.48  sim_ac_normalised:                      0
% 7.59/1.48  sim_smt_subsumption:                    0
% 7.59/1.48  
%------------------------------------------------------------------------------
