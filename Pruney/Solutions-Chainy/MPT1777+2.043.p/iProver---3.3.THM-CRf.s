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
% DateTime   : Thu Dec  3 12:23:33 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  216 (2102 expanded)
%              Number of clauses        :  127 ( 484 expanded)
%              Number of leaves         :   27 ( 915 expanded)
%              Depth                    :   20
%              Number of atoms          : 1005 (27774 expanded)
%              Number of equality atoms :  292 (4179 expanded)
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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f52,f51,f50,f49,f48,f47,f46])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f27])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1108,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1128,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2342,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1128])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1801,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

cnf(c_1802,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_2550,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2342,c_41,c_1802])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1129,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2555,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2550,c_1129])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1130,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2656,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2555,c_1130])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1110,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2341,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1128])).

cnf(c_1799,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

cnf(c_1800,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_2542,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2341,c_41,c_1800])).

cnf(c_2547,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_1129])).

cnf(c_2653,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2547,c_1130])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1121,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3623,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2653,c_1121])).

cnf(c_6684,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3623,c_41,c_1800])).

cnf(c_6685,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6684])).

cnf(c_6692,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_6685])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_46,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1123,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4011,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1123])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4017,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4011,c_25])).

cnf(c_4447,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4017,c_39,c_40,c_41,c_45])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1124,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5164,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4447,c_1124])).

cnf(c_12008,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6692,c_39,c_40,c_41,c_45,c_46,c_5164])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1133,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12013,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12008,c_1133])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1122,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1127,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4172,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1127])).

cnf(c_4218,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4172,c_41,c_1802])).

cnf(c_4219,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4218])).

cnf(c_4226,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_4219])).

cnf(c_3619,plain,
    ( m1_pre_topc(sK3,X0) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2653,c_1121])).

cnf(c_6657,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_3619])).

cnf(c_6696,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK3)
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6685,c_1133])).

cnf(c_10447,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_6696])).

cnf(c_10462,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10447,c_2656])).

cnf(c_12879,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12013,c_39,c_40,c_41,c_45,c_46,c_1800,c_1802,c_4226,c_5164,c_6657,c_10462])).

cnf(c_12901,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_12879,c_2656])).

cnf(c_8,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10487,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_491,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1507,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | X0 != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_5669,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_8369,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5669])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1116,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1185,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1116,c_22])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_1119,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1120,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1347,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1119,c_1120])).

cnf(c_7605,plain,
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
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1347])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1106,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2221,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1106,c_1129])).

cnf(c_2454,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2221,c_1130])).

cnf(c_7623,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7605,c_2454,c_2653,c_2656])).

cnf(c_7641,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,k2_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
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
    inference(predicate_to_equality_rev,[status(thm)],[c_7623])).

cnf(c_5244,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5164])).

cnf(c_10,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_12,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_275,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_12])).

cnf(c_4360,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_482,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2207,plain,
    ( k2_struct_0(X0) = k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_4157,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1533,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | X1 != u1_struct_0(sK2)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_1591,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | m1_subset_1(sK5,X0)
    | X0 != u1_struct_0(sK2)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_3817,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | m1_subset_1(sK5,k2_struct_0(sK2))
    | k2_struct_0(sK2) != u1_struct_0(sK2)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1831,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_2179,plain,
    ( X0 = u1_struct_0(X1)
    | X0 != k2_struct_0(X1)
    | u1_struct_0(X1) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_2771,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0)
    | k2_struct_0(X0) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_3816,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK2) = u1_struct_0(sK2)
    | k2_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1114,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3608,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2653,c_1114])).

cnf(c_3617,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3608])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1112,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2792,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2454,c_1112])).

cnf(c_3607,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2653,c_2792])).

cnf(c_3616,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3607])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1113,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2791,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2454,c_1113])).

cnf(c_3606,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2653,c_2791])).

cnf(c_3615,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3606])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2668,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_29])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12901,c_10487,c_8369,c_7641,c_5244,c_4360,c_4157,c_3817,c_3816,c_3617,c_3616,c_3615,c_2668,c_2656,c_1799,c_20,c_22,c_23,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:11:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.99  
% 3.77/0.99  ------  iProver source info
% 3.77/0.99  
% 3.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.99  git: non_committed_changes: false
% 3.77/0.99  git: last_make_outside_of_git: false
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  ------ Parsing...
% 3.77/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.99  ------ Proving...
% 3.77/0.99  ------ Problem Properties 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  clauses                                 37
% 3.77/0.99  conjectures                             19
% 3.77/0.99  EPR                                     20
% 3.77/0.99  Horn                                    33
% 3.77/0.99  unary                                   20
% 3.77/0.99  binary                                  3
% 3.77/0.99  lits                                    115
% 3.77/0.99  lits eq                                 5
% 3.77/0.99  fd_pure                                 0
% 3.77/0.99  fd_pseudo                               0
% 3.77/0.99  fd_cond                                 0
% 3.77/0.99  fd_pseudo_cond                          1
% 3.77/0.99  AC symbols                              0
% 3.77/0.99  
% 3.77/0.99  ------ Input Options Time Limit: Unbounded
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  Current options:
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ Proving...
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS status Theorem for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  fof(f16,conjecture,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f17,negated_conjecture,(
% 3.77/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.77/0.99    inference(negated_conjecture,[],[f16])).
% 3.77/0.99  
% 3.77/0.99  fof(f39,plain,(
% 3.77/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f17])).
% 3.77/0.99  
% 3.77/0.99  fof(f40,plain,(
% 3.77/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.77/0.99    inference(flattening,[],[f39])).
% 3.77/0.99  
% 3.77/0.99  fof(f52,plain,(
% 3.77/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f51,plain,(
% 3.77/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f50,plain,(
% 3.77/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f49,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f48,plain,(
% 3.77/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f47,plain,(
% 3.77/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f46,plain,(
% 3.77/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f53,plain,(
% 3.77/0.99    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f52,f51,f50,f49,f48,f47,f46])).
% 3.77/0.99  
% 3.77/0.99  fof(f81,plain,(
% 3.77/0.99    m1_pre_topc(sK2,sK0)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f5,axiom,(
% 3.77/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f22,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f5])).
% 3.77/0.99  
% 3.77/0.99  fof(f60,plain,(
% 3.77/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f22])).
% 3.77/0.99  
% 3.77/0.99  fof(f76,plain,(
% 3.77/0.99    l1_pre_topc(sK0)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f4,axiom,(
% 3.77/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f21,plain,(
% 3.77/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f4])).
% 3.77/0.99  
% 3.77/0.99  fof(f59,plain,(
% 3.77/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f21])).
% 3.77/0.99  
% 3.77/0.99  fof(f3,axiom,(
% 3.77/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f20,plain,(
% 3.77/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f3])).
% 3.77/0.99  
% 3.77/0.99  fof(f58,plain,(
% 3.77/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f20])).
% 3.77/0.99  
% 3.77/0.99  fof(f83,plain,(
% 3.77/0.99    m1_pre_topc(sK3,sK0)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f13,axiom,(
% 3.77/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f34,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f13])).
% 3.77/0.99  
% 3.77/0.99  fof(f70,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f34])).
% 3.77/0.99  
% 3.77/0.99  fof(f74,plain,(
% 3.77/0.99    ~v2_struct_0(sK0)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f75,plain,(
% 3.77/0.99    v2_pre_topc(sK0)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f80,plain,(
% 3.77/0.99    ~v2_struct_0(sK2)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f11,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f31,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f11])).
% 3.77/0.99  
% 3.77/0.99  fof(f32,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.77/0.99    inference(flattening,[],[f31])).
% 3.77/0.99  
% 3.77/0.99  fof(f68,plain,(
% 3.77/0.99    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f32])).
% 3.77/0.99  
% 3.77/0.99  fof(f87,plain,(
% 3.77/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f10,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f29,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f10])).
% 3.77/0.99  
% 3.77/0.99  fof(f30,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.77/0.99    inference(flattening,[],[f29])).
% 3.77/0.99  
% 3.77/0.99  fof(f67,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f30])).
% 3.77/0.99  
% 3.77/0.99  fof(f1,axiom,(
% 3.77/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f41,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f1])).
% 3.77/0.99  
% 3.77/0.99  fof(f42,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(flattening,[],[f41])).
% 3.77/0.99  
% 3.77/0.99  fof(f56,plain,(
% 3.77/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f42])).
% 3.77/0.99  
% 3.77/0.99  fof(f12,axiom,(
% 3.77/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f33,plain,(
% 3.77/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f12])).
% 3.77/0.99  
% 3.77/0.99  fof(f69,plain,(
% 3.77/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f33])).
% 3.77/0.99  
% 3.77/0.99  fof(f6,axiom,(
% 3.77/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f23,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f6])).
% 3.77/0.99  
% 3.77/0.99  fof(f61,plain,(
% 3.77/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f23])).
% 3.77/0.99  
% 3.77/0.99  fof(f7,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f24,plain,(
% 3.77/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f7])).
% 3.77/0.99  
% 3.77/0.99  fof(f25,plain,(
% 3.77/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.99    inference(flattening,[],[f24])).
% 3.77/0.99  
% 3.77/0.99  fof(f62,plain,(
% 3.77/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f25])).
% 3.77/0.99  
% 3.77/0.99  fof(f91,plain,(
% 3.77/0.99    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f90,plain,(
% 3.77/0.99    sK5 = sK6),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f15,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f37,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f15])).
% 3.77/0.99  
% 3.77/0.99  fof(f38,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.77/0.99    inference(flattening,[],[f37])).
% 3.77/0.99  
% 3.77/0.99  fof(f45,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.77/0.99    inference(nnf_transformation,[],[f38])).
% 3.77/0.99  
% 3.77/0.99  fof(f73,plain,(
% 3.77/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f45])).
% 3.77/0.99  
% 3.77/0.99  fof(f98,plain,(
% 3.77/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.77/0.99    inference(equality_resolution,[],[f73])).
% 3.77/0.99  
% 3.77/0.99  fof(f14,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f35,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f14])).
% 3.77/0.99  
% 3.77/0.99  fof(f36,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.99    inference(flattening,[],[f35])).
% 3.77/0.99  
% 3.77/0.99  fof(f71,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f36])).
% 3.77/0.99  
% 3.77/0.99  fof(f79,plain,(
% 3.77/0.99    l1_pre_topc(sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f8,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f26,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f8])).
% 3.77/0.99  
% 3.77/0.99  fof(f27,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.99    inference(flattening,[],[f26])).
% 3.77/0.99  
% 3.77/0.99  fof(f43,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.99    inference(nnf_transformation,[],[f27])).
% 3.77/0.99  
% 3.77/0.99  fof(f44,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.99    inference(flattening,[],[f43])).
% 3.77/0.99  
% 3.77/0.99  fof(f64,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f44])).
% 3.77/0.99  
% 3.77/0.99  fof(f96,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.99    inference(equality_resolution,[],[f64])).
% 3.77/0.99  
% 3.77/0.99  fof(f9,axiom,(
% 3.77/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f28,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f9])).
% 3.77/0.99  
% 3.77/0.99  fof(f66,plain,(
% 3.77/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f28])).
% 3.77/0.99  
% 3.77/0.99  fof(f88,plain,(
% 3.77/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f85,plain,(
% 3.77/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f86,plain,(
% 3.77/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f2,axiom,(
% 3.77/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.77/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f18,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/0.99    inference(ennf_transformation,[],[f2])).
% 3.77/0.99  
% 3.77/0.99  fof(f19,plain,(
% 3.77/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/0.99    inference(flattening,[],[f18])).
% 3.77/0.99  
% 3.77/0.99  fof(f57,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f19])).
% 3.77/0.99  
% 3.77/0.99  fof(f92,plain,(
% 3.77/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f89,plain,(
% 3.77/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f84,plain,(
% 3.77/0.99    v1_funct_1(sK4)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f82,plain,(
% 3.77/0.99    ~v2_struct_0(sK3)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f78,plain,(
% 3.77/0.99    v2_pre_topc(sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  fof(f77,plain,(
% 3.77/0.99    ~v2_struct_0(sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f53])).
% 3.77/0.99  
% 3.77/0.99  cnf(c_31,negated_conjecture,
% 3.77/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1108,plain,
% 3.77/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6,plain,
% 3.77/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1128,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top
% 3.77/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2342,plain,
% 3.77/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1108,c_1128]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_36,negated_conjecture,
% 3.77/0.99      ( l1_pre_topc(sK0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_41,plain,
% 3.77/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1801,plain,
% 3.77/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.77/0.99      inference(resolution,[status(thm)],[c_6,c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1802,plain,
% 3.77/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2550,plain,
% 3.77/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_2342,c_41,c_1802]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5,plain,
% 3.77/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1129,plain,
% 3.77/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2555,plain,
% 3.77/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2550,c_1129]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4,plain,
% 3.77/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1130,plain,
% 3.77/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.77/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2656,plain,
% 3.77/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2555,c_1130]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_29,negated_conjecture,
% 3.77/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1110,plain,
% 3.77/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2341,plain,
% 3.77/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1110,c_1128]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1799,plain,
% 3.77/0.99      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.77/0.99      inference(resolution,[status(thm)],[c_6,c_29]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1800,plain,
% 3.77/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2542,plain,
% 3.77/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_2341,c_41,c_1800]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2547,plain,
% 3.77/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2542,c_1129]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2653,plain,
% 3.77/0.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2547,c_1130]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_16,plain,
% 3.77/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.77/0.99      | ~ l1_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1121,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3623,plain,
% 3.77/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/0.99      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2653,c_1121]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6684,plain,
% 3.77/0.99      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.77/0.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_3623,c_41,c_1800]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6685,plain,
% 3.77/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/0.99      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_6684]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6692,plain,
% 3.77/0.99      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/0.99      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2656,c_6685]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_38,negated_conjecture,
% 3.77/0.99      ( ~ v2_struct_0(sK0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_39,plain,
% 3.77/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_37,negated_conjecture,
% 3.77/0.99      ( v2_pre_topc(sK0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_40,plain,
% 3.77/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_32,negated_conjecture,
% 3.77/0.99      ( ~ v2_struct_0(sK2) ),
% 3.77/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_45,plain,
% 3.77/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_46,plain,
% 3.77/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14,plain,
% 3.77/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | v2_struct_0(X1)
% 3.77/0.99      | v2_struct_0(X0)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X1)
% 3.77/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1123,plain,
% 3.77/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 3.77/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.77/0.99      | v2_struct_0(X1) = iProver_top
% 3.77/0.99      | v2_struct_0(X0) = iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top
% 3.77/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4011,plain,
% 3.77/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 3.77/0.99      | v2_struct_0(sK0) = iProver_top
% 3.77/0.99      | v2_struct_0(sK2) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1108,c_1123]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_25,negated_conjecture,
% 3.77/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.77/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4017,plain,
% 3.77/0.99      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 3.77/0.99      | v2_struct_0(sK0) = iProver_top
% 3.77/0.99      | v2_struct_0(sK2) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_4011,c_25]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4447,plain,
% 3.77/0.99      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_4017,c_39,c_40,c_41,c_45]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_13,plain,
% 3.77/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ m1_pre_topc(X2,X1)
% 3.77/0.99      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 3.77/0.99      | v2_struct_0(X1)
% 3.77/0.99      | v2_struct_0(X0)
% 3.77/0.99      | v2_struct_0(X2)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1124,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.77/0.99      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 3.77/0.99      | v2_struct_0(X1) = iProver_top
% 3.77/0.99      | v2_struct_0(X0) = iProver_top
% 3.77/0.99      | v2_struct_0(X2) = iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top
% 3.77/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5164,plain,
% 3.77/0.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.77/0.99      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.77/0.99      | v2_struct_0(sK0) = iProver_top
% 3.77/0.99      | v2_struct_0(sK2) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_4447,c_1124]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12008,plain,
% 3.77/0.99      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_6692,c_39,c_40,c_41,c_45,c_46,c_5164]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_0,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.77/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1133,plain,
% 3.77/0.99      ( X0 = X1
% 3.77/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.77/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12013,plain,
% 3.77/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.77/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_12008,c_1133]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_15,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1122,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.77/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.77/0.99      | ~ l1_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1127,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.77/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4172,plain,
% 3.77/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.77/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_25,c_1127]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4218,plain,
% 3.77/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/0.99      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_4172,c_41,c_1802]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4219,plain,
% 3.77/0.99      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.77/0.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_4218]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4226,plain,
% 3.77/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1122,c_4219]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3619,plain,
% 3.77/0.99      ( m1_pre_topc(sK3,X0) != iProver_top
% 3.77/0.99      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 3.77/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2653,c_1121]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6657,plain,
% 3.77/0.99      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.77/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2656,c_3619]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_6696,plain,
% 3.77/0.99      ( u1_struct_0(X0) = k2_struct_0(sK3)
% 3.77/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.77/0.99      | r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_6685,c_1133]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10447,plain,
% 3.77/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK3)
% 3.77/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2656,c_6696]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10462,plain,
% 3.77/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.77/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/0.99      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_10447,c_2656]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12879,plain,
% 3.77/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_12013,c_39,c_40,c_41,c_45,c_46,c_1800,c_1802,c_4226,
% 3.77/0.99                 c_5164,c_6657,c_10462]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12901,plain,
% 3.77/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_12879,c_2656]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8,plain,
% 3.77/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.77/0.99      | ~ l1_pre_topc(X0)
% 3.77/0.99      | ~ v2_pre_topc(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10487,plain,
% 3.77/0.99      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.77/0.99      | ~ l1_pre_topc(sK3)
% 3.77/0.99      | ~ v2_pre_topc(sK3) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_491,plain,
% 3.77/0.99      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 3.77/0.99      theory(equality) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1507,plain,
% 3.77/0.99      ( v3_pre_topc(X0,X1)
% 3.77/0.99      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.77/0.99      | X0 != k2_struct_0(X1) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_491]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5669,plain,
% 3.77/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.77/0.99      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.77/0.99      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_1507]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8369,plain,
% 3.77/0.99      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.77/0.99      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.77/0.99      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_5669]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_21,negated_conjecture,
% 3.77/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.77/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1116,plain,
% 3.77/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_22,negated_conjecture,
% 3.77/0.99      ( sK5 = sK6 ),
% 3.77/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1185,plain,
% 3.77/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_1116,c_22]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_18,plain,
% 3.77/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.77/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.77/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.77/0.99      | ~ v1_tsep_1(X4,X0)
% 3.77/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.77/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.77/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.77/0.99      | ~ m1_pre_topc(X4,X5)
% 3.77/0.99      | ~ m1_pre_topc(X4,X0)
% 3.77/0.99      | ~ m1_pre_topc(X0,X5)
% 3.77/0.99      | ~ v1_funct_1(X2)
% 3.77/0.99      | v2_struct_0(X5)
% 3.77/0.99      | v2_struct_0(X1)
% 3.77/0.99      | v2_struct_0(X4)
% 3.77/0.99      | v2_struct_0(X0)
% 3.77/0.99      | ~ l1_pre_topc(X5)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X5)
% 3.77/0.99      | ~ v2_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1119,plain,
% 3.77/0.99      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.77/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.77/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.77/0.99      | v1_tsep_1(X4,X0) != iProver_top
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.77/0.99      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.77/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.77/0.99      | m1_pre_topc(X4,X5) != iProver_top
% 3.77/0.99      | m1_pre_topc(X4,X0) != iProver_top
% 3.77/0.99      | m1_pre_topc(X0,X5) != iProver_top
% 3.77/0.99      | v1_funct_1(X2) != iProver_top
% 3.77/0.99      | v2_struct_0(X5) = iProver_top
% 3.77/0.99      | v2_struct_0(X1) = iProver_top
% 3.77/0.99      | v2_struct_0(X4) = iProver_top
% 3.77/0.99      | v2_struct_0(X0) = iProver_top
% 3.77/0.99      | l1_pre_topc(X5) != iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top
% 3.77/0.99      | v2_pre_topc(X5) != iProver_top
% 3.77/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17,plain,
% 3.77/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ m1_pre_topc(X2,X0)
% 3.77/0.99      | m1_pre_topc(X2,X1)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1120,plain,
% 3.77/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.77/0.99      | m1_pre_topc(X2,X1) = iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top
% 3.77/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1347,plain,
% 3.77/0.99      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.77/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.77/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.77/0.99      | v1_tsep_1(X4,X0) != iProver_top
% 3.77/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.77/0.99      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.77/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.77/0.99      | m1_pre_topc(X4,X0) != iProver_top
% 3.77/0.99      | m1_pre_topc(X0,X5) != iProver_top
% 3.77/0.99      | v1_funct_1(X2) != iProver_top
% 3.77/0.99      | v2_struct_0(X5) = iProver_top
% 3.77/0.99      | v2_struct_0(X1) = iProver_top
% 3.77/0.99      | v2_struct_0(X4) = iProver_top
% 3.77/0.99      | v2_struct_0(X0) = iProver_top
% 3.77/0.99      | l1_pre_topc(X5) != iProver_top
% 3.77/0.99      | l1_pre_topc(X1) != iProver_top
% 3.77/0.99      | v2_pre_topc(X5) != iProver_top
% 3.77/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.77/0.99      inference(forward_subsumption_resolution,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_1119,c_1120]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7605,plain,
% 3.77/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.77/0.99      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.77/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.77/0.99      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.77/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.77/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.77/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.77/0.99      | v1_funct_1(sK4) != iProver_top
% 3.77/0.99      | v2_struct_0(sK0) = iProver_top
% 3.77/0.99      | v2_struct_0(sK2) = iProver_top
% 3.77/0.99      | v2_struct_0(sK1) = iProver_top
% 3.77/0.99      | v2_struct_0(sK3) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1185,c_1347]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_33,negated_conjecture,
% 3.77/0.99      ( l1_pre_topc(sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1106,plain,
% 3.77/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2221,plain,
% 3.77/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1106,c_1129]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2454,plain,
% 3.77/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2221,c_1130]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7623,plain,
% 3.77/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.77/0.99      | v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
% 3.77/0.99      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.77/0.99      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
% 3.77/0.99      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 3.77/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.77/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.77/0.99      | v1_funct_1(sK4) != iProver_top
% 3.77/0.99      | v2_struct_0(sK0) = iProver_top
% 3.77/0.99      | v2_struct_0(sK2) = iProver_top
% 3.77/0.99      | v2_struct_0(sK1) = iProver_top
% 3.77/0.99      | v2_struct_0(sK3) = iProver_top
% 3.77/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.77/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.77/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 3.77/0.99      inference(light_normalisation,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_7605,c_2454,c_2653,c_2656]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7641,plain,
% 3.77/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.77/0.99      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
% 3.77/0.99      | ~ v1_tsep_1(sK2,sK3)
% 3.77/0.99      | ~ m1_subset_1(sK5,k2_struct_0(sK2))
% 3.77/0.99      | ~ m1_subset_1(sK5,k2_struct_0(sK3))
% 3.77/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
% 3.77/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.77/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.77/0.99      | ~ v1_funct_1(sK4)
% 3.77/0.99      | v2_struct_0(sK0)
% 3.77/0.99      | v2_struct_0(sK2)
% 3.77/0.99      | v2_struct_0(sK1)
% 3.77/0.99      | v2_struct_0(sK3)
% 3.77/0.99      | ~ l1_pre_topc(sK0)
% 3.77/0.99      | ~ l1_pre_topc(sK1)
% 3.77/0.99      | ~ v2_pre_topc(sK0)
% 3.77/0.99      | ~ v2_pre_topc(sK1) ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_7623]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_5244,plain,
% 3.77/0.99      ( ~ m1_pre_topc(sK2,sK0)
% 3.77/0.99      | m1_pre_topc(sK2,sK3)
% 3.77/0.99      | v2_struct_0(sK0)
% 3.77/0.99      | v2_struct_0(sK2)
% 3.77/0.99      | ~ l1_pre_topc(sK0)
% 3.77/0.99      | ~ v2_pre_topc(sK0) ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5164]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10,plain,
% 3.77/0.99      ( v1_tsep_1(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.77/0.99      | ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12,plain,
% 3.77/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/0.99      | ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ l1_pre_topc(X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_275,plain,
% 3.77/0.99      ( v1_tsep_1(X0,X1)
% 3.77/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.77/0.99      | ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X1) ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_10,c_12]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4360,plain,
% 3.77/0.99      ( v1_tsep_1(sK2,sK3)
% 3.77/0.99      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.77/0.99      | ~ m1_pre_topc(sK2,sK3)
% 3.77/0.99      | ~ l1_pre_topc(sK3)
% 3.77/0.99      | ~ v2_pre_topc(sK3) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_275]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_482,plain,( X0 = X0 ),theory(equality) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2207,plain,
% 3.77/0.99      ( k2_struct_0(X0) = k2_struct_0(X0) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_482]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_4157,plain,
% 3.77/0.99      ( k2_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_2207]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_493,plain,
% 3.77/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.77/0.99      theory(equality) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1533,plain,
% 3.77/0.99      ( m1_subset_1(X0,X1)
% 3.77/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 3.77/0.99      | X1 != u1_struct_0(sK2)
% 3.77/0.99      | X0 != sK6 ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_493]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1591,plain,
% 3.77/0.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 3.77/0.99      | m1_subset_1(sK5,X0)
% 3.77/0.99      | X0 != u1_struct_0(sK2)
% 3.77/0.99      | sK5 != sK6 ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_1533]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3817,plain,
% 3.77/0.99      ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 3.77/0.99      | m1_subset_1(sK5,k2_struct_0(sK2))
% 3.77/0.99      | k2_struct_0(sK2) != u1_struct_0(sK2)
% 3.77/0.99      | sK5 != sK6 ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_1591]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_483,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1831,plain,
% 3.77/0.99      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_483]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2179,plain,
% 3.77/0.99      ( X0 = u1_struct_0(X1)
% 3.77/0.99      | X0 != k2_struct_0(X1)
% 3.77/0.99      | u1_struct_0(X1) != k2_struct_0(X1) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_1831]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2771,plain,
% 3.77/0.99      ( u1_struct_0(X0) != k2_struct_0(X0)
% 3.77/0.99      | k2_struct_0(X0) = u1_struct_0(X0)
% 3.77/0.99      | k2_struct_0(X0) != k2_struct_0(X0) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_2179]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3816,plain,
% 3.77/0.99      ( u1_struct_0(sK2) != k2_struct_0(sK2)
% 3.77/0.99      | k2_struct_0(sK2) = u1_struct_0(sK2)
% 3.77/0.99      | k2_struct_0(sK2) != k2_struct_0(sK2) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_2771]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_24,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1114,plain,
% 3.77/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3608,plain,
% 3.77/0.99      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_2653,c_1114]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3617,plain,
% 3.77/0.99      ( m1_subset_1(sK5,k2_struct_0(sK3)) ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3608]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_27,negated_conjecture,
% 3.77/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1112,plain,
% 3.77/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2792,plain,
% 3.77/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_2454,c_1112]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3607,plain,
% 3.77/0.99      ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_2653,c_2792]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3616,plain,
% 3.77/0.99      ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3607]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_26,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1113,plain,
% 3.77/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2791,plain,
% 3.77/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_2454,c_1113]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3606,plain,
% 3.77/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.77/0.99      inference(demodulation,[status(thm)],[c_2653,c_2791]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3615,plain,
% 3.77/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
% 3.77/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3606]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3,plain,
% 3.77/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.77/0.99      | ~ l1_pre_topc(X1)
% 3.77/0.99      | ~ v2_pre_topc(X1)
% 3.77/0.99      | v2_pre_topc(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2668,plain,
% 3.77/0.99      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 3.77/0.99      inference(resolution,[status(thm)],[c_3,c_29]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_20,negated_conjecture,
% 3.77/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.77/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_23,negated_conjecture,
% 3.77/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_28,negated_conjecture,
% 3.77/0.99      ( v1_funct_1(sK4) ),
% 3.77/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_30,negated_conjecture,
% 3.77/0.99      ( ~ v2_struct_0(sK3) ),
% 3.77/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_34,negated_conjecture,
% 3.77/0.99      ( v2_pre_topc(sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_35,negated_conjecture,
% 3.77/0.99      ( ~ v2_struct_0(sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(contradiction,plain,
% 3.77/0.99      ( $false ),
% 3.77/0.99      inference(minisat,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_12901,c_10487,c_8369,c_7641,c_5244,c_4360,c_4157,
% 3.77/0.99                 c_3817,c_3816,c_3617,c_3616,c_3615,c_2668,c_2656,c_1799,
% 3.77/0.99                 c_20,c_22,c_23,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,
% 3.77/0.99                 c_36,c_37,c_38]) ).
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  ------                               Statistics
% 3.77/0.99  
% 3.77/0.99  ------ Selected
% 3.77/0.99  
% 3.77/0.99  total_time:                             0.367
% 3.77/0.99  
%------------------------------------------------------------------------------
