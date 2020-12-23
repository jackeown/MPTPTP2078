%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:33 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  179 (1536 expanded)
%              Number of clauses        :  100 ( 356 expanded)
%              Number of leaves         :   21 ( 657 expanded)
%              Depth                    :   20
%              Number of atoms          :  855 (19816 expanded)
%              Number of equality atoms :  162 (2869 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f47,f46,f45,f44,f43,f42,f41])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f31])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1088,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1106,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2316,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1106])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1765,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_30])).

cnf(c_1766,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1765])).

cnf(c_2501,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2316,c_40,c_1766])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1107,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2506,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2501,c_1107])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1108,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2614,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2506,c_1108])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1090,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2315,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1106])).

cnf(c_1763,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

cnf(c_1764,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1763])).

cnf(c_2493,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2315,c_40,c_1764])).

cnf(c_2498,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2493,c_1107])).

cnf(c_2611,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2498,c_1108])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1101,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3532,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2611,c_1101])).

cnf(c_6599,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3532,c_40,c_1764])).

cnf(c_6600,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6599])).

cnf(c_6607,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_6600])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1102,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_266,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_6])).

cnf(c_267,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_1080,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_2945,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1080])).

cnf(c_3085,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2945,c_40,c_1766])).

cnf(c_3086,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3085])).

cnf(c_3093,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_3086])).

cnf(c_10954,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6607,c_40,c_1766,c_3093])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1111,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10959,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10954,c_1111])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1105,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4497,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_1105])).

cnf(c_3925,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2614,c_24])).

cnf(c_4529,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4497,c_3925])).

cnf(c_4962,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4529,c_40,c_1766])).

cnf(c_4963,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4962])).

cnf(c_4971,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_4963])).

cnf(c_3529,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2611,c_1101])).

cnf(c_6390,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_3529])).

cnf(c_6611,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK3)
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6600,c_1111])).

cnf(c_10043,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2614,c_6611])).

cnf(c_10058,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10043,c_2614])).

cnf(c_11431,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10959,c_40,c_1764,c_1766,c_3093,c_4971,c_6390,c_10058])).

cnf(c_11450,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_11431,c_2614])).

cnf(c_9,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9060,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_483,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1463,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | X0 != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_5383,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_8219,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5383])).

cnf(c_11,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_13,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_275,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_13])).

cnf(c_5759,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_17,plain,
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
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2048,plain,
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
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2231,plain,
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
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2048])).

cnf(c_2864,plain,
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
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_4074,plain,
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
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2864])).

cnf(c_3094,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3093])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2626,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_28])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1095,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1140,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1095,c_21])).

cnf(c_1354,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1140])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1096,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1163,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1096,c_21])).

cnf(c_1333,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1163])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11450,c_9060,c_8219,c_5759,c_4074,c_3094,c_2626,c_1765,c_1763,c_1354,c_1333,c_19,c_23,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.54/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.99  
% 3.54/0.99  ------  iProver source info
% 3.54/0.99  
% 3.54/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.99  git: non_committed_changes: false
% 3.54/0.99  git: last_make_outside_of_git: false
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  ------ Parsing...
% 3.54/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.99  ------ Proving...
% 3.54/0.99  ------ Problem Properties 
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  clauses                                 36
% 3.54/0.99  conjectures                             19
% 3.54/0.99  EPR                                     20
% 3.54/0.99  Horn                                    34
% 3.54/0.99  unary                                   20
% 3.54/0.99  binary                                  3
% 3.54/0.99  lits                                    105
% 3.54/0.99  lits eq                                 4
% 3.54/0.99  fd_pure                                 0
% 3.54/0.99  fd_pseudo                               0
% 3.54/0.99  fd_cond                                 0
% 3.54/0.99  fd_pseudo_cond                          1
% 3.54/0.99  AC symbols                              0
% 3.54/0.99  
% 3.54/0.99  ------ Input Options Time Limit: Unbounded
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  Current options:
% 3.54/0.99  ------ 
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ Proving...
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS status Theorem for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  fof(f14,conjecture,(
% 3.54/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f15,negated_conjecture,(
% 3.54/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.54/0.99    inference(negated_conjecture,[],[f14])).
% 3.54/0.99  
% 3.54/0.99  fof(f33,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f15])).
% 3.54/0.99  
% 3.54/0.99  fof(f34,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.54/0.99    inference(flattening,[],[f33])).
% 3.54/0.99  
% 3.54/0.99  fof(f47,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f46,plain,(
% 3.54/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f45,plain,(
% 3.54/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f44,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f43,plain,(
% 3.54/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f42,plain,(
% 3.54/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f41,plain,(
% 3.54/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f48,plain,(
% 3.54/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.54/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f34,f47,f46,f45,f44,f43,f42,f41])).
% 3.54/0.99  
% 3.54/0.99  fof(f75,plain,(
% 3.54/0.99    m1_pre_topc(sK2,sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f5,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f20,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f5])).
% 3.54/0.99  
% 3.54/0.99  fof(f55,plain,(
% 3.54/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f20])).
% 3.54/0.99  
% 3.54/0.99  fof(f70,plain,(
% 3.54/0.99    l1_pre_topc(sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f4,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f19,plain,(
% 3.54/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f4])).
% 3.54/0.99  
% 3.54/0.99  fof(f54,plain,(
% 3.54/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f19])).
% 3.54/0.99  
% 3.54/0.99  fof(f3,axiom,(
% 3.54/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f18,plain,(
% 3.54/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f3])).
% 3.54/0.99  
% 3.54/0.99  fof(f53,plain,(
% 3.54/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f18])).
% 3.54/0.99  
% 3.54/0.99  fof(f77,plain,(
% 3.54/0.99    m1_pre_topc(sK3,sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f11,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f28,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f11])).
% 3.54/0.99  
% 3.54/0.99  fof(f64,plain,(
% 3.54/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f28])).
% 3.54/0.99  
% 3.54/0.99  fof(f10,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f27,plain,(
% 3.54/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f10])).
% 3.54/0.99  
% 3.54/0.99  fof(f63,plain,(
% 3.54/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f27])).
% 3.54/0.99  
% 3.54/0.99  fof(f81,plain,(
% 3.54/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f6,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f21,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f6])).
% 3.54/0.99  
% 3.54/0.99  fof(f37,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(nnf_transformation,[],[f21])).
% 3.54/0.99  
% 3.54/0.99  fof(f56,plain,(
% 3.54/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f37])).
% 3.54/0.99  
% 3.54/0.99  fof(f1,axiom,(
% 3.54/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f35,plain,(
% 3.54/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.99    inference(nnf_transformation,[],[f1])).
% 3.54/0.99  
% 3.54/0.99  fof(f36,plain,(
% 3.54/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.99    inference(flattening,[],[f35])).
% 3.54/0.99  
% 3.54/0.99  fof(f51,plain,(
% 3.54/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f36])).
% 3.54/0.99  
% 3.54/0.99  fof(f57,plain,(
% 3.54/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f37])).
% 3.54/0.99  
% 3.54/0.99  fof(f7,axiom,(
% 3.54/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f22,plain,(
% 3.54/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f7])).
% 3.54/0.99  
% 3.54/0.99  fof(f23,plain,(
% 3.54/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.99    inference(flattening,[],[f22])).
% 3.54/0.99  
% 3.54/0.99  fof(f58,plain,(
% 3.54/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f23])).
% 3.54/0.99  
% 3.54/0.99  fof(f8,axiom,(
% 3.54/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f24,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f8])).
% 3.54/0.99  
% 3.54/0.99  fof(f25,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.99    inference(flattening,[],[f24])).
% 3.54/0.99  
% 3.54/0.99  fof(f38,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.99    inference(nnf_transformation,[],[f25])).
% 3.54/0.99  
% 3.54/0.99  fof(f39,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.99    inference(flattening,[],[f38])).
% 3.54/0.99  
% 3.54/0.99  fof(f60,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f39])).
% 3.54/0.99  
% 3.54/0.99  fof(f90,plain,(
% 3.54/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.99    inference(equality_resolution,[],[f60])).
% 3.54/0.99  
% 3.54/0.99  fof(f9,axiom,(
% 3.54/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f26,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/0.99    inference(ennf_transformation,[],[f9])).
% 3.54/0.99  
% 3.54/0.99  fof(f62,plain,(
% 3.54/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f26])).
% 3.54/0.99  
% 3.54/0.99  fof(f13,axiom,(
% 3.54/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f31,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f13])).
% 3.54/0.99  
% 3.54/0.99  fof(f32,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.99    inference(flattening,[],[f31])).
% 3.54/0.99  
% 3.54/0.99  fof(f40,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/0.99    inference(nnf_transformation,[],[f32])).
% 3.54/0.99  
% 3.54/0.99  fof(f67,plain,(
% 3.54/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f40])).
% 3.54/0.99  
% 3.54/0.99  fof(f92,plain,(
% 3.54/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/0.99    inference(equality_resolution,[],[f67])).
% 3.54/0.99  
% 3.54/0.99  fof(f2,axiom,(
% 3.54/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f16,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/0.99    inference(ennf_transformation,[],[f2])).
% 3.54/0.99  
% 3.54/0.99  fof(f17,plain,(
% 3.54/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/0.99    inference(flattening,[],[f16])).
% 3.54/0.99  
% 3.54/0.99  fof(f52,plain,(
% 3.54/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f17])).
% 3.54/0.99  
% 3.54/0.99  fof(f83,plain,(
% 3.54/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f84,plain,(
% 3.54/0.99    sK5 = sK6),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f85,plain,(
% 3.54/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f86,plain,(
% 3.54/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f82,plain,(
% 3.54/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f80,plain,(
% 3.54/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f79,plain,(
% 3.54/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f78,plain,(
% 3.54/0.99    v1_funct_1(sK4)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f76,plain,(
% 3.54/0.99    ~v2_struct_0(sK3)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f74,plain,(
% 3.54/0.99    ~v2_struct_0(sK2)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f73,plain,(
% 3.54/0.99    l1_pre_topc(sK1)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f72,plain,(
% 3.54/0.99    v2_pre_topc(sK1)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f71,plain,(
% 3.54/0.99    ~v2_struct_0(sK1)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f69,plain,(
% 3.54/0.99    v2_pre_topc(sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  fof(f68,plain,(
% 3.54/0.99    ~v2_struct_0(sK0)),
% 3.54/0.99    inference(cnf_transformation,[],[f48])).
% 3.54/0.99  
% 3.54/0.99  cnf(c_30,negated_conjecture,
% 3.54/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1088,plain,
% 3.54/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1106,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2316,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1088,c_1106]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_35,negated_conjecture,
% 3.54/0.99      ( l1_pre_topc(sK0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_40,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1765,plain,
% 3.54/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_6,c_30]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1766,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1765]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2501,plain,
% 3.54/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2316,c_40,c_1766]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5,plain,
% 3.54/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1107,plain,
% 3.54/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2506,plain,
% 3.54/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2501,c_1107]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4,plain,
% 3.54/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1108,plain,
% 3.54/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.54/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2614,plain,
% 3.54/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2506,c_1108]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_28,negated_conjecture,
% 3.54/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1090,plain,
% 3.54/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2315,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1090,c_1106]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1763,plain,
% 3.54/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_6,c_28]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1764,plain,
% 3.54/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_1763]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2493,plain,
% 3.54/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2315,c_40,c_1764]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2498,plain,
% 3.54/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2493,c_1107]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2611,plain,
% 3.54/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2498,c_1108]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_15,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1101,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3532,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.54/0.99      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2611,c_1101]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6599,plain,
% 3.54/0.99      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_3532,c_40,c_1764]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6600,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.54/0.99      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_6599]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6607,plain,
% 3.54/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.54/0.99      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2614,c_6600]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_14,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1102,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_24,negated_conjecture,
% 3.54/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.54/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_266,plain,
% 3.54/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8,c_6]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_267,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_266]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1080,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2945,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK3) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_24,c_1080]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3085,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2945,c_40,c_1766]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3086,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_3085]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3093,plain,
% 3.54/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1102,c_3086]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10954,plain,
% 3.54/0.99      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_6607,c_40,c_1766,c_3093]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_0,plain,
% 3.54/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.54/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1111,plain,
% 3.54/0.99      ( X0 = X1
% 3.54/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.54/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10959,plain,
% 3.54/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.54/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_10954,c_1111]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1105,plain,
% 3.54/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.54/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.54/0.99      | l1_pre_topc(X1) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4497,plain,
% 3.54/0.99      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK2) = iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2614,c_1105]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3925,plain,
% 3.54/0.99      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_2614,c_24]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4529,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_4497,c_3925]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4962,plain,
% 3.54/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_4529,c_40,c_1766]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4963,plain,
% 3.54/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.54/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_4962]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4971,plain,
% 3.54/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1102,c_4963]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3529,plain,
% 3.54/0.99      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.54/0.99      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 3.54/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2611,c_1101]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6390,plain,
% 3.54/0.99      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.54/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 3.54/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2614,c_3529]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6611,plain,
% 3.54/0.99      ( u1_struct_0(X0) = k2_struct_0(sK3)
% 3.54/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/0.99      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_6600,c_1111]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10043,plain,
% 3.54/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK3)
% 3.54/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.54/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2614,c_6611]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10058,plain,
% 3.54/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.54/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.54/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_10043,c_2614]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11431,plain,
% 3.54/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_10959,c_40,c_1764,c_1766,c_3093,c_4971,c_6390,c_10058]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11450,plain,
% 3.54/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_11431,c_2614]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9,plain,
% 3.54/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | ~ v2_pre_topc(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9060,plain,
% 3.54/0.99      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.54/0.99      | ~ l1_pre_topc(sK3)
% 3.54/0.99      | ~ v2_pre_topc(sK3) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_483,plain,
% 3.54/0.99      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 3.54/0.99      theory(equality) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1463,plain,
% 3.54/0.99      ( v3_pre_topc(X0,X1)
% 3.54/0.99      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.54/0.99      | X0 != k2_struct_0(X1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_483]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5383,plain,
% 3.54/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/0.99      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.54/0.99      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_1463]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8219,plain,
% 3.54/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.54/0.99      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.54/0.99      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_5383]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_11,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_13,plain,
% 3.54/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ l1_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_275,plain,
% 3.54/0.99      ( v1_tsep_1(X0,X1)
% 3.54/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X1) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_11,c_13]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5759,plain,
% 3.54/0.99      ( v1_tsep_1(sK2,sK3)
% 3.54/0.99      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.54/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.54/0.99      | ~ l1_pre_topc(sK3)
% 3.54/0.99      | ~ v2_pre_topc(sK3) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_275]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_17,plain,
% 3.54/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.54/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/0.99      | ~ v1_tsep_1(X4,X0)
% 3.54/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_pre_topc(X4,X5)
% 3.54/0.99      | ~ m1_pre_topc(X4,X0)
% 3.54/0.99      | ~ m1_pre_topc(X0,X5)
% 3.54/0.99      | v2_struct_0(X5)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X4)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | ~ v1_funct_1(X2)
% 3.54/0.99      | ~ l1_pre_topc(X5)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X5)
% 3.54/0.99      | ~ v2_pre_topc(X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2048,plain,
% 3.54/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.54/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.54/0.99      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
% 3.54/0.99      | ~ v1_tsep_1(X0,X3)
% 3.54/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.54/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.54/0.99      | ~ m1_pre_topc(X0,X3)
% 3.54/0.99      | ~ m1_pre_topc(X0,X2)
% 3.54/0.99      | ~ m1_pre_topc(X3,X2)
% 3.54/0.99      | v2_struct_0(X3)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X2)
% 3.54/0.99      | ~ v1_funct_1(sK4)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(X2)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X2) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2231,plain,
% 3.54/0.99      ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
% 3.54/0.99      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.54/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.54/0.99      | ~ v1_tsep_1(X0,sK3)
% 3.54/0.99      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 3.54/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.54/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.54/0.99      | ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ m1_pre_topc(X0,sK3)
% 3.54/0.99      | ~ m1_pre_topc(sK3,X1)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(X1)
% 3.54/0.99      | v2_struct_0(sK1)
% 3.54/0.99      | v2_struct_0(sK3)
% 3.54/0.99      | ~ v1_funct_1(sK4)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ l1_pre_topc(sK1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(sK1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2048]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2864,plain,
% 3.54/0.99      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
% 3.54/0.99      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.54/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.54/0.99      | ~ v1_tsep_1(sK2,sK3)
% 3.54/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.54/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.54/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.54/0.99      | ~ m1_pre_topc(sK2,X0)
% 3.54/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.54/0.99      | ~ m1_pre_topc(sK3,X0)
% 3.54/0.99      | v2_struct_0(X0)
% 3.54/0.99      | v2_struct_0(sK2)
% 3.54/0.99      | v2_struct_0(sK1)
% 3.54/0.99      | v2_struct_0(sK3)
% 3.54/0.99      | ~ v1_funct_1(sK4)
% 3.54/0.99      | ~ l1_pre_topc(X0)
% 3.54/0.99      | ~ l1_pre_topc(sK1)
% 3.54/0.99      | ~ v2_pre_topc(X0)
% 3.54/0.99      | ~ v2_pre_topc(sK1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2231]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4074,plain,
% 3.54/0.99      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 3.54/0.99      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.54/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 3.54/0.99      | ~ v1_tsep_1(sK2,sK3)
% 3.54/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.54/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.54/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.54/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.54/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.54/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.54/0.99      | v2_struct_0(sK0)
% 3.54/0.99      | v2_struct_0(sK2)
% 3.54/0.99      | v2_struct_0(sK1)
% 3.54/0.99      | v2_struct_0(sK3)
% 3.54/0.99      | ~ v1_funct_1(sK4)
% 3.54/0.99      | ~ l1_pre_topc(sK0)
% 3.54/0.99      | ~ l1_pre_topc(sK1)
% 3.54/0.99      | ~ v2_pre_topc(sK0)
% 3.54/0.99      | ~ v2_pre_topc(sK1) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2864]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3094,plain,
% 3.54/0.99      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3093]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3,plain,
% 3.54/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.54/0.99      | ~ l1_pre_topc(X1)
% 3.54/0.99      | ~ v2_pre_topc(X1)
% 3.54/0.99      | v2_pre_topc(X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2626,plain,
% 3.54/0.99      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_3,c_28]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_22,negated_conjecture,
% 3.54/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1095,plain,
% 3.54/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_21,negated_conjecture,
% 3.54/0.99      ( sK5 = sK6 ),
% 3.54/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1140,plain,
% 3.54/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1095,c_21]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1354,plain,
% 3.54/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1140]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_20,negated_conjecture,
% 3.54/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.54/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1096,plain,
% 3.54/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1163,plain,
% 3.54/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1096,c_21]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1333,plain,
% 3.54/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1163]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_19,negated_conjecture,
% 3.54/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.54/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_23,negated_conjecture,
% 3.54/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_25,negated_conjecture,
% 3.54/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.54/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_26,negated_conjecture,
% 3.54/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_27,negated_conjecture,
% 3.54/0.99      ( v1_funct_1(sK4) ),
% 3.54/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_29,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK3) ),
% 3.54/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_31,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK2) ),
% 3.54/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_32,negated_conjecture,
% 3.54/0.99      ( l1_pre_topc(sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_33,negated_conjecture,
% 3.54/0.99      ( v2_pre_topc(sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_34,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_36,negated_conjecture,
% 3.54/0.99      ( v2_pre_topc(sK0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_37,negated_conjecture,
% 3.54/0.99      ( ~ v2_struct_0(sK0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(contradiction,plain,
% 3.54/0.99      ( $false ),
% 3.54/0.99      inference(minisat,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_11450,c_9060,c_8219,c_5759,c_4074,c_3094,c_2626,
% 3.54/0.99                 c_1765,c_1763,c_1354,c_1333,c_19,c_23,c_25,c_26,c_27,
% 3.54/0.99                 c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  ------                               Statistics
% 3.54/0.99  
% 3.54/0.99  ------ Selected
% 3.54/0.99  
% 3.54/0.99  total_time:                             0.338
% 3.54/0.99  
%------------------------------------------------------------------------------
