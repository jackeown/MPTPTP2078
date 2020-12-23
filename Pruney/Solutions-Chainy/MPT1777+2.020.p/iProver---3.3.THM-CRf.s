%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:28 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  236 (2073 expanded)
%              Number of clauses        :  141 ( 526 expanded)
%              Number of leaves         :   24 ( 876 expanded)
%              Depth                    :   24
%              Number of atoms          : 1141 (27592 expanded)
%              Number of equality atoms :  321 (4149 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f46,f57,f56,f55,f54,f53,f52,f51])).

fof(f89,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(nnf_transformation,[],[f44])).

fof(f81,plain,(
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

fof(f104,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f97,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_539,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1280,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_564,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1257,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_2424,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1257])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_44,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2029,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_564,c_539])).

cnf(c_2030,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_2666,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2424,c_44,c_2030])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_565,plain,
    ( l1_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1256,plain,
    ( l1_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_2671,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2666,c_1256])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_566,plain,
    ( ~ l1_struct_0(X0_55)
    | k2_struct_0(X0_55) = u1_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1255,plain,
    ( k2_struct_0(X0_55) = u1_struct_0(X0_55)
    | l1_struct_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_3450,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2671,c_1255])).

cnf(c_8,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_561,plain,
    ( v3_pre_topc(k2_struct_0(X0_55),X0_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1260,plain,
    ( v3_pre_topc(k2_struct_0(X0_55),X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_3739,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_1260])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_43,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_567,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1254,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_2210,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1254])).

cnf(c_5373,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3739,c_43,c_44,c_2030,c_2210])).

cnf(c_12,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_16,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_299,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_16])).

cnf(c_531,plain,
    ( v1_tsep_1(X0_55,X1_55)
    | ~ v3_pre_topc(u1_struct_0(X0_55),X1_55)
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_299])).

cnf(c_1288,plain,
    ( v1_tsep_1(X0_55,X1_55) = iProver_top
    | v3_pre_topc(u1_struct_0(X0_55),X1_55) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_6241,plain,
    ( v1_tsep_1(sK2,sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5373,c_1288])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_541,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1278,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_2423,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1257])).

cnf(c_2027,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_564,c_541])).

cnf(c_2028,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_2650,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_44,c_2028])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_568,plain,
    ( ~ l1_pre_topc(X0_55)
    | ~ v1_pre_topc(X0_55)
    | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) = X0_55 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1253,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) = X0_55
    | l1_pre_topc(X0_55) != iProver_top
    | v1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_2656,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2650,c_1253])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_48,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_545,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_563,plain,
    ( v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1258,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_3025,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_1258])).

cnf(c_3666,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_44,c_48,c_2030,c_3025])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_324,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_4])).

cnf(c_325,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_529,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_pre_topc(X2_55,X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ l1_pre_topc(X3_55)
    | g1_pre_topc(u1_struct_0(X3_55),u1_pre_topc(X3_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
    | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_1290,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
    | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != g1_pre_topc(u1_struct_0(X3_55),u1_pre_topc(X3_55))
    | m1_pre_topc(X3_55,X1_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_8261,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
    | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != sK3
    | m1_pre_topc(X1_55,X2_55) = iProver_top
    | m1_pre_topc(X0_55,sK2) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_1290])).

cnf(c_8972,plain,
    ( l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK2) != iProver_top
    | m1_pre_topc(X1_55,X2_55) = iProver_top
    | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != sK3
    | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8261,c_44,c_2030])).

cnf(c_8973,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
    | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != sK3
    | m1_pre_topc(X1_55,X2_55) = iProver_top
    | m1_pre_topc(X0_55,sK2) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_8972])).

cnf(c_8982,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
    | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
    | m1_pre_topc(X0_55,X1_55) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_8973])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_556,plain,
    ( m1_pre_topc(X0_55,X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1265,plain,
    ( m1_pre_topc(X0_55,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_560,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1261,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_3745,plain,
    ( m1_pre_topc(sK2,X0_55) != iProver_top
    | m1_pre_topc(sK3,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_1261])).

cnf(c_3938,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_3745])).

cnf(c_8983,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
    | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
    | m1_pre_topc(X0_55,X1_55) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_3666,c_8973])).

cnf(c_9055,plain,
    ( m1_pre_topc(X0_55,X1_55) = iProver_top
    | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
    | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8982,c_44,c_2030,c_3938,c_8983])).

cnf(c_9056,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
    | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
    | m1_pre_topc(X0_55,X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_9055])).

cnf(c_9064,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
    | m1_pre_topc(sK2,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_9056])).

cnf(c_9171,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | m1_pre_topc(sK2,X0_55) = iProver_top
    | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9064,c_44,c_2030])).

cnf(c_9172,plain,
    ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
    | m1_pre_topc(sK2,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_9171])).

cnf(c_9181,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3666,c_9172])).

cnf(c_9197,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9181,c_44,c_2028])).

cnf(c_4394,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3938,c_44,c_2030])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_553,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | m1_pre_topc(X2_55,X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1268,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_4399,plain,
    ( m1_pre_topc(X0_55,sK2) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4394,c_1268])).

cnf(c_4856,plain,
    ( m1_pre_topc(X0_55,sK2) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4399,c_43,c_44,c_2030,c_2210])).

cnf(c_9210,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9197,c_4856])).

cnf(c_18455,plain,
    ( v1_tsep_1(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6241,c_43,c_44,c_2030,c_2210,c_9210])).

cnf(c_18,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_555,plain,
    ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X1_55,X2_55)
    | ~ v2_pre_topc(X2_55)
    | ~ l1_pre_topc(X2_55) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1266,plain,
    ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_1435,plain,
    ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1266,c_1268])).

cnf(c_9940,plain,
    ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_1435])).

cnf(c_10405,plain,
    ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9940,c_43,c_44])).

cnf(c_15,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X0,X2)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_558,plain,
    ( ~ r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_tsep_1(X0_55,X2_55)
    | v1_tsep_1(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_pre_topc(X1_55,X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ v2_pre_topc(X2_55)
    | ~ l1_pre_topc(X2_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1263,plain,
    ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_tsep_1(X0_55,X2_55) != iProver_top
    | v1_tsep_1(X0_55,X1_55) = iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X2_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_10413,plain,
    ( v1_tsep_1(X0_55,X1_55) != iProver_top
    | v1_tsep_1(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_10405,c_1263])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_50,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_11816,plain,
    ( v2_struct_0(X1_55) = iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | v1_tsep_1(X0_55,sK3) = iProver_top
    | v1_tsep_1(X0_55,X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10413,c_50])).

cnf(c_11817,plain,
    ( v1_tsep_1(X0_55,X1_55) != iProver_top
    | v1_tsep_1(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_11816])).

cnf(c_11830,plain,
    ( v1_tsep_1(X0_55,X1_55) != iProver_top
    | v1_tsep_1(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11817,c_1268])).

cnf(c_18461,plain,
    ( v1_tsep_1(sK2,sK3) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_18455,c_11830])).

cnf(c_21,plain,
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
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_552,plain,
    ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56)
    | ~ r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56)
    | ~ v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_tsep_1(X2_55,X0_55)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_56,u1_struct_0(X2_55))
    | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_10161,plain,
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
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_10164,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
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
    inference(predicate_to_equality,[status(thm)],[c_10161])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_547,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1273,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_25,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_548,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1315,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1273,c_548])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_549,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1272,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_1340,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1272,c_548])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_58,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_55,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_53,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_52,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_51,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_49,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_47,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_46,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_45,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18461,c_10164,c_9181,c_3938,c_2210,c_2030,c_2028,c_1315,c_1340,c_58,c_55,c_54,c_53,c_52,c_51,c_50,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.99  
% 3.84/0.99  ------  iProver source info
% 3.84/0.99  
% 3.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.99  git: non_committed_changes: false
% 3.84/0.99  git: last_make_outside_of_git: false
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  ------ Parsing...
% 3.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.99  ------ Proving...
% 3.84/0.99  ------ Problem Properties 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  clauses                                 40
% 3.84/0.99  conjectures                             19
% 3.84/0.99  EPR                                     18
% 3.84/0.99  Horn                                    36
% 3.84/0.99  unary                                   19
% 3.84/0.99  binary                                  3
% 3.84/0.99  lits                                    134
% 3.84/0.99  lits eq                                 6
% 3.84/0.99  fd_pure                                 0
% 3.84/0.99  fd_pseudo                               0
% 3.84/0.99  fd_cond                                 0
% 3.84/0.99  fd_pseudo_cond                          0
% 3.84/0.99  AC symbols                              0
% 3.84/0.99  
% 3.84/0.99  ------ Input Options Time Limit: Unbounded
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  Current options:
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ Proving...
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS status Theorem for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  fof(f17,conjecture,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f18,negated_conjecture,(
% 3.84/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.84/0.99    inference(negated_conjecture,[],[f17])).
% 3.84/0.99  
% 3.84/0.99  fof(f45,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f46,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.84/0.99    inference(flattening,[],[f45])).
% 3.84/0.99  
% 3.84/0.99  fof(f57,plain,(
% 3.84/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f56,plain,(
% 3.84/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f55,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f54,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f53,plain,(
% 3.84/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f52,plain,(
% 3.84/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f51,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f58,plain,(
% 3.84/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f46,f57,f56,f55,f54,f53,f52,f51])).
% 3.84/0.99  
% 3.84/0.99  fof(f89,plain,(
% 3.84/0.99    m1_pre_topc(sK2,sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f5,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f25,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f5])).
% 3.84/0.99  
% 3.84/0.99  fof(f63,plain,(
% 3.84/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f84,plain,(
% 3.84/0.99    l1_pre_topc(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f4,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f24,plain,(
% 3.84/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f4])).
% 3.84/0.99  
% 3.84/0.99  fof(f62,plain,(
% 3.84/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f24])).
% 3.84/0.99  
% 3.84/0.99  fof(f3,axiom,(
% 3.84/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f23,plain,(
% 3.84/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f3])).
% 3.84/0.99  
% 3.84/0.99  fof(f61,plain,(
% 3.84/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f23])).
% 3.84/0.99  
% 3.84/0.99  fof(f8,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f30,plain,(
% 3.84/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f8])).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f30])).
% 3.84/0.99  
% 3.84/0.99  fof(f67,plain,(
% 3.84/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f31])).
% 3.84/0.99  
% 3.84/0.99  fof(f83,plain,(
% 3.84/0.99    v2_pre_topc(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f21,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f22,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f21])).
% 3.84/0.99  
% 3.84/0.99  fof(f60,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f22])).
% 3.84/0.99  
% 3.84/0.99  fof(f10,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f10])).
% 3.84/0.99  
% 3.84/0.99  fof(f34,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f47,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f48,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f71,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f48])).
% 3.84/0.99  
% 3.84/0.99  fof(f102,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(equality_resolution,[],[f71])).
% 3.84/0.99  
% 3.84/0.99  fof(f12,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f12])).
% 3.84/0.99  
% 3.84/0.99  fof(f75,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f37])).
% 3.84/0.99  
% 3.84/0.99  fof(f91,plain,(
% 3.84/0.99    m1_pre_topc(sK3,sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f19,plain,(
% 3.84/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f20,plain,(
% 3.84/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f19])).
% 3.84/0.99  
% 3.84/0.99  fof(f59,plain,(
% 3.84/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f20])).
% 3.84/0.99  
% 3.84/0.99  fof(f88,plain,(
% 3.84/0.99    ~v2_struct_0(sK2)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f95,plain,(
% 3.84/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f6,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f26,plain,(
% 3.84/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f6])).
% 3.84/0.99  
% 3.84/0.99  fof(f27,plain,(
% 3.84/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.99    inference(flattening,[],[f26])).
% 3.84/0.99  
% 3.84/0.99  fof(f65,plain,(
% 3.84/0.99    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f7,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f7])).
% 3.84/0.99  
% 3.84/0.99  fof(f29,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f66,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f29])).
% 3.84/0.99  
% 3.84/0.99  fof(f13,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f13])).
% 3.84/0.99  
% 3.84/0.99  fof(f76,plain,(
% 3.84/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f38])).
% 3.84/0.99  
% 3.84/0.99  fof(f9,axiom,(
% 3.84/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f9])).
% 3.84/0.99  
% 3.84/0.99  fof(f69,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f32])).
% 3.84/0.99  
% 3.84/0.99  fof(f15,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f41,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f42,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f41])).
% 3.84/0.99  
% 3.84/0.99  fof(f79,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f42])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f40,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(flattening,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f49,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f40])).
% 3.84/0.99  
% 3.84/0.99  fof(f78,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f49])).
% 3.84/0.99  
% 3.84/0.99  fof(f11,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f35,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f11])).
% 3.84/0.99  
% 3.84/0.99  fof(f36,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.99    inference(flattening,[],[f35])).
% 3.84/0.99  
% 3.84/0.99  fof(f73,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f90,plain,(
% 3.84/0.99    ~v2_struct_0(sK3)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f16,axiom,(
% 3.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f43,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f16])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.99    inference(flattening,[],[f43])).
% 3.84/0.99  
% 3.84/0.99  fof(f50,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f44])).
% 3.84/0.99  
% 3.84/0.99  fof(f81,plain,(
% 3.84/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f50])).
% 3.84/0.99  
% 3.84/0.99  fof(f104,plain,(
% 3.84/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.84/0.99    inference(equality_resolution,[],[f81])).
% 3.84/0.99  
% 3.84/0.99  fof(f97,plain,(
% 3.84/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f98,plain,(
% 3.84/0.99    sK5 = sK6),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f99,plain,(
% 3.84/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f100,plain,(
% 3.84/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f96,plain,(
% 3.84/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f94,plain,(
% 3.84/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f93,plain,(
% 3.84/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f92,plain,(
% 3.84/0.99    v1_funct_1(sK4)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f87,plain,(
% 3.84/0.99    l1_pre_topc(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f86,plain,(
% 3.84/0.99    v2_pre_topc(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f85,plain,(
% 3.84/0.99    ~v2_struct_0(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f82,plain,(
% 3.84/0.99    ~v2_struct_0(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_34,negated_conjecture,
% 3.84/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_539,negated_conjecture,
% 3.84/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_34]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1280,plain,
% 3.84/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_564,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.84/0.99      | ~ l1_pre_topc(X1_55)
% 3.84/0.99      | l1_pre_topc(X0_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1257,plain,
% 3.84/0.99      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2424,plain,
% 3.84/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1280,c_1257]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_39,negated_conjecture,
% 3.84/0.99      ( l1_pre_topc(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_44,plain,
% 3.84/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2029,plain,
% 3.84/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.84/0.99      inference(resolution,[status(thm)],[c_564,c_539]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2030,plain,
% 3.84/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2666,plain,
% 3.84/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2424,c_44,c_2030]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3,plain,
% 3.84/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_565,plain,
% 3.84/0.99      ( l1_struct_0(X0_55) | ~ l1_pre_topc(X0_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1256,plain,
% 3.84/0.99      ( l1_struct_0(X0_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2671,plain,
% 3.84/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2666,c_1256]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2,plain,
% 3.84/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_566,plain,
% 3.84/0.99      ( ~ l1_struct_0(X0_55) | k2_struct_0(X0_55) = u1_struct_0(X0_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1255,plain,
% 3.84/0.99      ( k2_struct_0(X0_55) = u1_struct_0(X0_55)
% 3.84/0.99      | l1_struct_0(X0_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3450,plain,
% 3.84/0.99      ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2671,c_1255]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8,plain,
% 3.84/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.84/0.99      | ~ v2_pre_topc(X0)
% 3.84/0.99      | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_561,plain,
% 3.84/0.99      ( v3_pre_topc(k2_struct_0(X0_55),X0_55)
% 3.84/0.99      | ~ v2_pre_topc(X0_55)
% 3.84/0.99      | ~ l1_pre_topc(X0_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1260,plain,
% 3.84/0.99      ( v3_pre_topc(k2_struct_0(X0_55),X0_55) = iProver_top
% 3.84/0.99      | v2_pre_topc(X0_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3739,plain,
% 3.84/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top
% 3.84/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3450,c_1260]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_40,negated_conjecture,
% 3.84/0.99      ( v2_pre_topc(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_43,plain,
% 3.84/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ v2_pre_topc(X1)
% 3.84/0.99      | v2_pre_topc(X0)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_567,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.84/0.99      | ~ v2_pre_topc(X1_55)
% 3.84/0.99      | v2_pre_topc(X0_55)
% 3.84/0.99      | ~ l1_pre_topc(X1_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1254,plain,
% 3.84/0.99      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/0.99      | v2_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | v2_pre_topc(X0_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2210,plain,
% 3.84/0.99      ( v2_pre_topc(sK0) != iProver_top
% 3.84/0.99      | v2_pre_topc(sK2) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1280,c_1254]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5373,plain,
% 3.84/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK2) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3739,c_43,c_44,c_2030,c_2210]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12,plain,
% 3.84/0.99      ( v1_tsep_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.84/0.99      | ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ v2_pre_topc(X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_16,plain,
% 3.84/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/0.99      | ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_299,plain,
% 3.84/0.99      ( v1_tsep_1(X0,X1)
% 3.84/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.84/0.99      | ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | ~ v2_pre_topc(X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_12,c_16]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_531,plain,
% 3.84/0.99      ( v1_tsep_1(X0_55,X1_55)
% 3.84/0.99      | ~ v3_pre_topc(u1_struct_0(X0_55),X1_55)
% 3.84/0.99      | ~ m1_pre_topc(X0_55,X1_55)
% 3.84/0.99      | ~ v2_pre_topc(X1_55)
% 3.84/0.99      | ~ l1_pre_topc(X1_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_299]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1288,plain,
% 3.84/0.99      ( v1_tsep_1(X0_55,X1_55) = iProver_top
% 3.84/0.99      | v3_pre_topc(u1_struct_0(X0_55),X1_55) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/0.99      | v2_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6241,plain,
% 3.84/0.99      ( v1_tsep_1(sK2,sK2) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.84/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5373,c_1288]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_32,negated_conjecture,
% 3.84/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_541,negated_conjecture,
% 3.84/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_32]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1278,plain,
% 3.84/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2423,plain,
% 3.84/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1278,c_1257]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2027,plain,
% 3.84/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.84/0.99      inference(resolution,[status(thm)],[c_564,c_541]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2028,plain,
% 3.84/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2027]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2650,plain,
% 3.84/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2423,c_44,c_2028]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_0,plain,
% 3.84/0.99      ( ~ l1_pre_topc(X0)
% 3.84/0.99      | ~ v1_pre_topc(X0)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.84/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_568,plain,
% 3.84/0.99      ( ~ l1_pre_topc(X0_55)
% 3.84/0.99      | ~ v1_pre_topc(X0_55)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) = X0_55 ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1253,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) = X0_55
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top
% 3.84/0.99      | v1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2656,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 3.84/0.99      | v1_pre_topc(sK3) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2650,c_1253]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_35,negated_conjecture,
% 3.84/0.99      ( ~ v2_struct_0(sK2) ),
% 3.84/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_48,plain,
% 3.84/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_28,negated_conjecture,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.84/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_545,negated_conjecture,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5,plain,
% 3.84/0.99      ( v2_struct_0(X0)
% 3.84/0.99      | ~ l1_pre_topc(X0)
% 3.84/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_563,plain,
% 3.84/0.99      ( v2_struct_0(X0_55)
% 3.84/0.99      | ~ l1_pre_topc(X0_55)
% 3.84/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1258,plain,
% 3.84/0.99      ( v2_struct_0(X0_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top
% 3.84/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3025,plain,
% 3.84/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.84/0.99      | v1_pre_topc(sK3) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_545,c_1258]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3666,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2656,c_44,c_48,c_2030,c_3025]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | m1_pre_topc(X2,X3)
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | ~ l1_pre_topc(X3)
% 3.84/0.99      | ~ l1_pre_topc(X2)
% 3.84/0.99      | ~ l1_pre_topc(X0)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_324,plain,
% 3.84/0.99      ( ~ l1_pre_topc(X2)
% 3.84/0.99      | ~ l1_pre_topc(X3)
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | m1_pre_topc(X2,X3)
% 3.84/0.99      | ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.84/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7,c_4]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_325,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | m1_pre_topc(X2,X3)
% 3.84/0.99      | ~ l1_pre_topc(X1)
% 3.84/0.99      | ~ l1_pre_topc(X2)
% 3.84/0.99      | ~ l1_pre_topc(X3)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_324]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_529,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.84/0.99      | m1_pre_topc(X2_55,X3_55)
% 3.84/0.99      | ~ l1_pre_topc(X1_55)
% 3.84/0.99      | ~ l1_pre_topc(X2_55)
% 3.84/0.99      | ~ l1_pre_topc(X3_55)
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X3_55),u1_pre_topc(X3_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_325]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1290,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != g1_pre_topc(u1_struct_0(X3_55),u1_pre_topc(X3_55))
% 3.84/0.99      | m1_pre_topc(X3_55,X1_55) != iProver_top
% 3.84/0.99      | m1_pre_topc(X2_55,X0_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X2_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8261,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != sK3
% 3.84/0.99      | m1_pre_topc(X1_55,X2_55) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0_55,sK2) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X2_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_545,c_1290]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8972,plain,
% 3.84/0.99      ( l1_pre_topc(X2_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | m1_pre_topc(X0_55,sK2) != iProver_top
% 3.84/0.99      | m1_pre_topc(X1_55,X2_55) = iProver_top
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != sK3
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_8261,c_44,c_2030]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8973,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X2_55),u1_pre_topc(X2_55)) != sK3
% 3.84/0.99      | m1_pre_topc(X1_55,X2_55) = iProver_top
% 3.84/0.99      | m1_pre_topc(X0_55,sK2) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X2_55) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_8972]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8982,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
% 3.84/0.99      | m1_pre_topc(X0_55,X1_55) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_545,c_8973]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_17,plain,
% 3.84/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_556,plain,
% 3.84/0.99      ( m1_pre_topc(X0_55,X0_55) | ~ l1_pre_topc(X0_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1265,plain,
% 3.84/0.99      ( m1_pre_topc(X0_55,X0_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.84/0.99      | ~ l1_pre_topc(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_560,plain,
% 3.84/0.99      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55)
% 3.84/0.99      | ~ l1_pre_topc(X1_55) ),
% 3.84/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1261,plain,
% 3.84/0.99      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)),X1_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3745,plain,
% 3.84/0.99      ( m1_pre_topc(sK2,X0_55) != iProver_top
% 3.84/0.99      | m1_pre_topc(sK3,X0_55) = iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_545,c_1261]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3938,plain,
% 3.84/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.84/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1265,c_3745]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8983,plain,
% 3.84/0.99      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
% 3.84/0.99      | m1_pre_topc(X0_55,X1_55) = iProver_top
% 3.84/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.84/0.99      | l1_pre_topc(X1_55) != iProver_top
% 3.84/0.99      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3666,c_8973]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_9055,plain,
% 3.84/0.99      ( m1_pre_topc(X0_55,X1_55) = iProver_top
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
% 3.84/0.99      | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_8982,c_44,c_2030,c_3938,c_8983]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9056,plain,
% 3.84/1.00      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
% 3.84/1.00      | g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)) != sK3
% 3.84/1.00      | m1_pre_topc(X0_55,X1_55) = iProver_top
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_9055]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9064,plain,
% 3.84/1.00      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
% 3.84/1.00      | m1_pre_topc(sK2,X0_55) = iProver_top
% 3.84/1.00      | l1_pre_topc(X0_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_545,c_9056]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9171,plain,
% 3.84/1.00      ( l1_pre_topc(X0_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK2,X0_55) = iProver_top
% 3.84/1.00      | g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3 ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_9064,c_44,c_2030]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9172,plain,
% 3.84/1.00      ( g1_pre_topc(u1_struct_0(X0_55),u1_pre_topc(X0_55)) != sK3
% 3.84/1.00      | m1_pre_topc(sK2,X0_55) = iProver_top
% 3.84/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_9171]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9181,plain,
% 3.84/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.84/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3666,c_9172]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9197,plain,
% 3.84/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_9181,c_44,c_2028]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4394,plain,
% 3.84/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_3938,c_44,c_2030]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_20,plain,
% 3.84/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.84/1.00      | ~ m1_pre_topc(X2,X0)
% 3.84/1.00      | m1_pre_topc(X2,X1)
% 3.84/1.00      | ~ v2_pre_topc(X1)
% 3.84/1.00      | ~ l1_pre_topc(X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_553,plain,
% 3.84/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.84/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 3.84/1.00      | m1_pre_topc(X2_55,X1_55)
% 3.84/1.00      | ~ v2_pre_topc(X1_55)
% 3.84/1.00      | ~ l1_pre_topc(X1_55) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1268,plain,
% 3.84/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X2_55,X1_55) = iProver_top
% 3.84/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4399,plain,
% 3.84/1.00      ( m1_pre_topc(X0_55,sK2) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.84/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.84/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4394,c_1268]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4856,plain,
% 3.84/1.00      ( m1_pre_topc(X0_55,sK2) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_4399,c_43,c_44,c_2030,c_2210]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9210,plain,
% 3.84/1.00      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_9197,c_4856]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18455,plain,
% 3.84/1.00      ( v1_tsep_1(sK2,sK2) = iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_6241,c_43,c_44,c_2030,c_2210,c_9210]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.84/1.00      | ~ m1_pre_topc(X0,X2)
% 3.84/1.00      | ~ m1_pre_topc(X1,X2)
% 3.84/1.00      | ~ m1_pre_topc(X0,X1)
% 3.84/1.00      | ~ v2_pre_topc(X2)
% 3.84/1.00      | ~ l1_pre_topc(X2) ),
% 3.84/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_555,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.84/1.00      | ~ m1_pre_topc(X0_55,X1_55)
% 3.84/1.00      | ~ m1_pre_topc(X0_55,X2_55)
% 3.84/1.00      | ~ m1_pre_topc(X1_55,X2_55)
% 3.84/1.00      | ~ v2_pre_topc(X2_55)
% 3.84/1.00      | ~ l1_pre_topc(X2_55) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1266,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 3.84/1.00      | v2_pre_topc(X2_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X2_55) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1435,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 3.84/1.00      | v2_pre_topc(X2_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X2_55) != iProver_top ),
% 3.84/1.00      inference(forward_subsumption_resolution,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_1266,c_1268]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9940,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(sK3)) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.84/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.84/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1278,c_1435]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10405,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(sK3)) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_9940,c_43,c_44]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15,plain,
% 3.84/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.84/1.00      | ~ v1_tsep_1(X0,X2)
% 3.84/1.00      | v1_tsep_1(X0,X1)
% 3.84/1.00      | ~ m1_pre_topc(X0,X2)
% 3.84/1.00      | ~ m1_pre_topc(X1,X2)
% 3.84/1.00      | v2_struct_0(X2)
% 3.84/1.00      | v2_struct_0(X1)
% 3.84/1.00      | ~ v2_pre_topc(X2)
% 3.84/1.00      | ~ l1_pre_topc(X2) ),
% 3.84/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_558,plain,
% 3.84/1.00      ( ~ r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.84/1.00      | ~ v1_tsep_1(X0_55,X2_55)
% 3.84/1.00      | v1_tsep_1(X0_55,X1_55)
% 3.84/1.00      | ~ m1_pre_topc(X0_55,X2_55)
% 3.84/1.00      | ~ m1_pre_topc(X1_55,X2_55)
% 3.84/1.00      | v2_struct_0(X1_55)
% 3.84/1.00      | v2_struct_0(X2_55)
% 3.84/1.00      | ~ v2_pre_topc(X2_55)
% 3.84/1.00      | ~ l1_pre_topc(X2_55) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1263,plain,
% 3.84/1.00      ( r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,X2_55) != iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,X1_55) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X1_55,X2_55) != iProver_top
% 3.84/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.84/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.84/1.00      | v2_pre_topc(X2_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X2_55) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10413,plain,
% 3.84/1.00      ( v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,sK3) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.84/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.84/1.00      | v2_struct_0(sK3) = iProver_top
% 3.84/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_10405,c_1263]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_33,negated_conjecture,
% 3.84/1.00      ( ~ v2_struct_0(sK3) ),
% 3.84/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_50,plain,
% 3.84/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11816,plain,
% 3.84/1.00      ( v2_struct_0(X1_55) = iProver_top
% 3.84/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,sK3) = iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.84/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_10413,c_50]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11817,plain,
% 3.84/1.00      ( v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,sK3) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.84/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.84/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_11816]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11830,plain,
% 3.84/1.00      ( v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.84/1.00      | v1_tsep_1(X0_55,sK3) = iProver_top
% 3.84/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.84/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.84/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.84/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.84/1.00      inference(forward_subsumption_resolution,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_11817,c_1268]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18461,plain,
% 3.84/1.00      ( v1_tsep_1(sK2,sK3) = iProver_top
% 3.84/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.84/1.00      | v2_struct_0(sK2) = iProver_top
% 3.84/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.84/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_18455,c_11830]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_21,plain,
% 3.84/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.84/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.84/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.84/1.00      | ~ v1_tsep_1(X4,X0)
% 3.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.84/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.84/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_pre_topc(X4,X5)
% 3.84/1.00      | ~ m1_pre_topc(X0,X5)
% 3.84/1.00      | ~ m1_pre_topc(X4,X0)
% 3.84/1.00      | ~ v1_funct_1(X2)
% 3.84/1.00      | v2_struct_0(X5)
% 3.84/1.00      | v2_struct_0(X4)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | v2_struct_0(X1)
% 3.84/1.00      | ~ v2_pre_topc(X5)
% 3.84/1.00      | ~ v2_pre_topc(X1)
% 3.84/1.00      | ~ l1_pre_topc(X5)
% 3.84/1.00      | ~ l1_pre_topc(X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_552,plain,
% 3.84/1.00      ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56)
% 3.84/1.00      | ~ r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56)
% 3.84/1.00      | ~ v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.84/1.00      | ~ v1_tsep_1(X2_55,X0_55)
% 3.84/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.84/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(X2_55))
% 3.84/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
% 3.84/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 3.84/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 3.84/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 3.84/1.00      | ~ v1_funct_1(X0_56)
% 3.84/1.00      | v2_struct_0(X0_55)
% 3.84/1.00      | v2_struct_0(X1_55)
% 3.84/1.00      | v2_struct_0(X3_55)
% 3.84/1.00      | v2_struct_0(X2_55)
% 3.84/1.00      | ~ v2_pre_topc(X1_55)
% 3.84/1.00      | ~ v2_pre_topc(X3_55)
% 3.84/1.00      | ~ l1_pre_topc(X1_55)
% 3.84/1.00      | ~ l1_pre_topc(X3_55) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10161,plain,
% 3.84/1.00      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 3.84/1.00      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.84/1.00      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.84/1.00      | ~ v1_tsep_1(sK2,sK3)
% 3.84/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.84/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.84/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.84/1.00      | ~ m1_pre_topc(sK2,sK3)
% 3.84/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.84/1.00      | ~ v1_funct_1(sK4)
% 3.84/1.00      | v2_struct_0(sK0)
% 3.84/1.00      | v2_struct_0(sK2)
% 3.84/1.00      | v2_struct_0(sK1)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v2_pre_topc(sK0)
% 3.84/1.00      | ~ v2_pre_topc(sK1)
% 3.84/1.00      | ~ l1_pre_topc(sK0)
% 3.84/1.00      | ~ l1_pre_topc(sK1) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_552]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10164,plain,
% 3.84/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != iProver_top
% 3.84/1.00      | r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.84/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.84/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.84/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.84/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.84/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.84/1.00      | v1_funct_1(sK4) != iProver_top
% 3.84/1.00      | v2_struct_0(sK0) = iProver_top
% 3.84/1.00      | v2_struct_0(sK2) = iProver_top
% 3.84/1.00      | v2_struct_0(sK1) = iProver_top
% 3.84/1.00      | v2_struct_0(sK3) = iProver_top
% 3.84/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.84/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.84/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.84/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_10161]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_26,negated_conjecture,
% 3.84/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_547,negated_conjecture,
% 3.84/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1273,plain,
% 3.84/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_25,negated_conjecture,
% 3.84/1.00      ( sK5 = sK6 ),
% 3.84/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_548,negated_conjecture,
% 3.84/1.00      ( sK5 = sK6 ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1315,plain,
% 3.84/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_1273,c_548]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_24,negated_conjecture,
% 3.84/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.84/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_549,negated_conjecture,
% 3.84/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1272,plain,
% 3.84/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1340,plain,
% 3.84/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_1272,c_548]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_23,negated_conjecture,
% 3.84/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.84/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_58,plain,
% 3.84/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_27,negated_conjecture,
% 3.84/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_55,plain,
% 3.84/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_29,negated_conjecture,
% 3.84/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_54,plain,
% 3.84/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_30,negated_conjecture,
% 3.84/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_53,plain,
% 3.84/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_31,negated_conjecture,
% 3.84/1.00      ( v1_funct_1(sK4) ),
% 3.84/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_52,plain,
% 3.84/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_51,plain,
% 3.84/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_49,plain,
% 3.84/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_36,negated_conjecture,
% 3.84/1.00      ( l1_pre_topc(sK1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_47,plain,
% 3.84/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_37,negated_conjecture,
% 3.84/1.00      ( v2_pre_topc(sK1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_46,plain,
% 3.84/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_38,negated_conjecture,
% 3.84/1.00      ( ~ v2_struct_0(sK1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_45,plain,
% 3.84/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_41,negated_conjecture,
% 3.84/1.00      ( ~ v2_struct_0(sK0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_42,plain,
% 3.84/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(contradiction,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(minisat,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_18461,c_10164,c_9181,c_3938,c_2210,c_2030,c_2028,
% 3.84/1.00                 c_1315,c_1340,c_58,c_55,c_54,c_53,c_52,c_51,c_50,c_49,
% 3.84/1.00                 c_48,c_47,c_46,c_45,c_44,c_43,c_42]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ Selected
% 3.84/1.00  
% 3.84/1.00  total_time:                             0.473
% 3.84/1.00  
%------------------------------------------------------------------------------
