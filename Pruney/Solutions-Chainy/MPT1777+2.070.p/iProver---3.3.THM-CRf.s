%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:39 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  235 (1729 expanded)
%              Number of clauses        :  148 ( 519 expanded)
%              Number of leaves         :   23 ( 671 expanded)
%              Depth                    :   25
%              Number of atoms          :  965 (20337 expanded)
%              Number of equality atoms :  276 (3061 expanded)
%              Maximal formula depth    :   32 (   5 average)
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f41])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f51,f50,f49,f48,f47,f46,f45])).

fof(f79,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_462,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1134,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_480,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1118,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_2281,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1118])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1957,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_480,c_462])).

cnf(c_1958,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1957])).

cnf(c_2424,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2281,c_38,c_1958])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_481,plain,
    ( l1_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1117,plain,
    ( l1_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_2429,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_1117])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_482,plain,
    ( ~ l1_struct_0(X0_55)
    | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1116,plain,
    ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
    | l1_struct_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_2669,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2429,c_1116])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_476,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1122,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_3617,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_1122])).

cnf(c_9095,plain,
    ( m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3617,c_38,c_1958])).

cnf(c_9096,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9095])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_470,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1128,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_19,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_469,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1194,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1128,c_469])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_473,plain,
    ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56)
    | ~ r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56)
    | ~ v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v3_pre_topc(X2_56,X0_55)
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ r1_tarski(X2_56,u1_struct_0(X2_55))
    | ~ m1_subset_1(X1_56,u1_struct_0(X2_55))
    | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X2_56,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r2_hidden(X1_56,X2_56)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1125,plain,
    ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56) = iProver_top
    | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v3_pre_topc(X2_56,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | r1_tarski(X2_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | r2_hidden(X1_56,X2_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_484,plain,
    ( m1_subset_1(X0_56,X1_56)
    | ~ m1_subset_1(X2_56,k1_zfmisc_1(X1_56))
    | ~ r2_hidden(X0_56,X2_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1114,plain,
    ( m1_subset_1(X0_56,X1_56) = iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(X1_56)) != iProver_top
    | r2_hidden(X0_56,X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_474,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | m1_pre_topc(X2_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1124,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_1289,plain,
    ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56) = iProver_top
    | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v3_pre_topc(X2_56,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | r1_tarski(X2_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
    | r2_hidden(X1_56,X2_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1125,c_1114,c_1124])).

cnf(c_5511,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v3_pre_topc(X0_56,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r1_tarski(X0_56,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK5,X0_56) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1289])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_458,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1138,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_2177,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1117])).

cnf(c_2349,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2177,c_1116])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_460,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1136,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_2282,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1118])).

cnf(c_1959,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_480,c_460])).

cnf(c_1960,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_2528,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2282,c_38,c_1960])).

cnf(c_2533,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_1117])).

cnf(c_3169,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2533,c_1116])).

cnf(c_5512,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
    | v3_pre_topc(X0_56,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | r1_tarski(X0_56,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK5,X0_56) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5511,c_2349,c_2669,c_3169])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_52,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_465,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1131,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_3174,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2349,c_1131])).

cnf(c_3598,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2669,c_3174])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_464,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1132,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_3175,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2349,c_1132])).

cnf(c_3599,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2669,c_3175])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_468,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1129,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_1169,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1129,c_469])).

cnf(c_3812,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3169,c_1169])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_475,plain,
    ( m1_pre_topc(X0_55,X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1123,plain,
    ( m1_pre_topc(X0_55,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_264,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_6])).

cnf(c_265,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_452,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_265])).

cnf(c_1144,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_4639,plain,
    ( m1_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0_55,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3169,c_1144])).

cnf(c_22,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_466,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3813,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3169,c_466])).

cnf(c_4690,plain,
    ( m1_pre_topc(X0_55,sK2) != iProver_top
    | m1_pre_topc(X0_55,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4639,c_3813])).

cnf(c_5036,plain,
    ( m1_pre_topc(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4690,c_38,c_1960])).

cnf(c_5037,plain,
    ( m1_pre_topc(X0_55,sK2) != iProver_top
    | m1_pre_topc(X0_55,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5036])).

cnf(c_5044,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_5037])).

cnf(c_5982,plain,
    ( r2_hidden(sK5,X0_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r1_tarski(X0_56,k2_struct_0(sK2)) != iProver_top
    | v3_pre_topc(X0_56,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5512,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_45,c_46,c_52,c_1960,c_3598,c_3599,c_3812,c_5044])).

cnf(c_5983,plain,
    ( v3_pre_topc(X0_56,sK3) != iProver_top
    | r1_tarski(X0_56,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | r2_hidden(sK5,X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_5982])).

cnf(c_9110,plain,
    ( v3_pre_topc(u1_struct_0(X0_55),sK3) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0_55),k2_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9096,c_5983])).

cnf(c_8,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_478,plain,
    ( m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1120,plain,
    ( m1_pre_topc(X0_55,X1_55) = iProver_top
    | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_2977,plain,
    ( m1_pre_topc(X0_55,sK2) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_466,c_1120])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_485,plain,
    ( r1_tarski(X0_56,X1_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1113,plain,
    ( r1_tarski(X0_56,X1_56) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_2848,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1113])).

cnf(c_5770,plain,
    ( m1_pre_topc(X0_55,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0_55),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3169,c_2848])).

cnf(c_9739,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | v3_pre_topc(u1_struct_0(X0_55),sK3) != iProver_top
    | r2_hidden(sK5,u1_struct_0(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9110,c_38,c_1960,c_2977,c_5770])).

cnf(c_9740,plain,
    ( v3_pre_topc(u1_struct_0(X0_55),sK3) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | r2_hidden(sK5,u1_struct_0(X0_55)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9739])).

cnf(c_9749,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_9740])).

cnf(c_9769,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9749,c_2669])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_477,plain,
    ( v3_pre_topc(k2_struct_0(X0_55),X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5251,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_5252,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5251])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_479,plain,
    ( v2_struct_0(X0_55)
    | ~ l1_struct_0(X0_55)
    | ~ v1_xboole_0(u1_struct_0(X0_55)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1119,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | l1_struct_0(X0_55) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_3619,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_1119])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_467,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1130,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | r2_hidden(X0_56,X1_56)
    | v1_xboole_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1112,plain,
    ( m1_subset_1(X0_56,X1_56) != iProver_top
    | r2_hidden(X0_56,X1_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1773,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1112])).

cnf(c_3600,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2669,c_1773])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_483,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2692,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_483,c_462])).

cnf(c_2693,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2692])).

cnf(c_2338,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2339,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_2066,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_2069,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9769,c_5252,c_3619,c_3600,c_2693,c_2339,c_2069,c_1958,c_44,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.53/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/1.00  
% 3.53/1.00  ------  iProver source info
% 3.53/1.00  
% 3.53/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.53/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/1.00  git: non_committed_changes: false
% 3.53/1.00  git: last_make_outside_of_git: false
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  ------ Parsing...
% 3.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/1.00  
% 3.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/1.00  ------ Proving...
% 3.53/1.00  ------ Problem Properties 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  clauses                                 35
% 3.53/1.00  conjectures                             19
% 3.53/1.00  EPR                                     19
% 3.53/1.00  Horn                                    32
% 3.53/1.00  unary                                   19
% 3.53/1.00  binary                                  4
% 3.53/1.00  lits                                    104
% 3.53/1.00  lits eq                                 3
% 3.53/1.00  fd_pure                                 0
% 3.53/1.00  fd_pseudo                               0
% 3.53/1.00  fd_cond                                 0
% 3.53/1.00  fd_pseudo_cond                          0
% 3.53/1.00  AC symbols                              0
% 3.53/1.00  
% 3.53/1.00  ------ Input Options Time Limit: Unbounded
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ 
% 3.53/1.00  Current options:
% 3.53/1.00  ------ 
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  ------ Proving...
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS status Theorem for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  fof(f16,conjecture,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f17,negated_conjecture,(
% 3.53/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.53/1.00    inference(negated_conjecture,[],[f16])).
% 3.53/1.00  
% 3.53/1.00  fof(f41,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f17])).
% 3.53/1.00  
% 3.53/1.00  fof(f42,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.53/1.00    inference(flattening,[],[f41])).
% 3.53/1.00  
% 3.53/1.00  fof(f51,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f50,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f49,plain,(
% 3.53/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f48,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f47,plain,(
% 3.53/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f46,plain,(
% 3.53/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f45,plain,(
% 3.53/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.53/1.00    introduced(choice_axiom,[])).
% 3.53/1.00  
% 3.53/1.00  fof(f52,plain,(
% 3.53/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f51,f50,f49,f48,f47,f46,f45])).
% 3.53/1.00  
% 3.53/1.00  fof(f79,plain,(
% 3.53/1.00    m1_pre_topc(sK3,sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f7,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f28,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f7])).
% 3.53/1.00  
% 3.53/1.00  fof(f59,plain,(
% 3.53/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f28])).
% 3.53/1.00  
% 3.53/1.00  fof(f72,plain,(
% 3.53/1.00    l1_pre_topc(sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f6,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f27,plain,(
% 3.53/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f6])).
% 3.53/1.00  
% 3.53/1.00  fof(f58,plain,(
% 3.53/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f27])).
% 3.53/1.00  
% 3.53/1.00  fof(f5,axiom,(
% 3.53/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f26,plain,(
% 3.53/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f5])).
% 3.53/1.00  
% 3.53/1.00  fof(f57,plain,(
% 3.53/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f26])).
% 3.53/1.00  
% 3.53/1.00  fof(f12,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f35,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f12])).
% 3.53/1.00  
% 3.53/1.00  fof(f65,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f35])).
% 3.53/1.00  
% 3.53/1.00  fof(f87,plain,(
% 3.53/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f86,plain,(
% 3.53/1.00    sK5 = sK6),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f15,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f39,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f15])).
% 3.53/1.00  
% 3.53/1.00  fof(f40,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.53/1.00    inference(flattening,[],[f39])).
% 3.53/1.00  
% 3.53/1.00  fof(f44,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f40])).
% 3.53/1.00  
% 3.53/1.00  fof(f69,plain,(
% 3.53/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f44])).
% 3.53/1.00  
% 3.53/1.00  fof(f89,plain,(
% 3.53/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.53/1.00    inference(equality_resolution,[],[f69])).
% 3.53/1.00  
% 3.53/1.00  fof(f3,axiom,(
% 3.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f22,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.53/1.00    inference(ennf_transformation,[],[f3])).
% 3.53/1.00  
% 3.53/1.00  fof(f23,plain,(
% 3.53/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.53/1.00    inference(flattening,[],[f22])).
% 3.53/1.00  
% 3.53/1.00  fof(f55,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f23])).
% 3.53/1.00  
% 3.53/1.00  fof(f14,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f37,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f14])).
% 3.53/1.00  
% 3.53/1.00  fof(f38,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f37])).
% 3.53/1.00  
% 3.53/1.00  fof(f67,plain,(
% 3.53/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f38])).
% 3.53/1.00  
% 3.53/1.00  fof(f75,plain,(
% 3.53/1.00    l1_pre_topc(sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f77,plain,(
% 3.53/1.00    m1_pre_topc(sK2,sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f70,plain,(
% 3.53/1.00    ~v2_struct_0(sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f71,plain,(
% 3.53/1.00    v2_pre_topc(sK0)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f73,plain,(
% 3.53/1.00    ~v2_struct_0(sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f74,plain,(
% 3.53/1.00    v2_pre_topc(sK1)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f76,plain,(
% 3.53/1.00    ~v2_struct_0(sK2)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f78,plain,(
% 3.53/1.00    ~v2_struct_0(sK3)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f80,plain,(
% 3.53/1.00    v1_funct_1(sK4)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f88,plain,(
% 3.53/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f82,plain,(
% 3.53/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f81,plain,(
% 3.53/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f85,plain,(
% 3.53/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f13,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f36,plain,(
% 3.53/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f13])).
% 3.53/1.00  
% 3.53/1.00  fof(f66,plain,(
% 3.53/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f36])).
% 3.53/1.00  
% 3.53/1.00  fof(f10,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f32,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f10])).
% 3.53/1.00  
% 3.53/1.00  fof(f43,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(nnf_transformation,[],[f32])).
% 3.53/1.00  
% 3.53/1.00  fof(f62,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f43])).
% 3.53/1.00  
% 3.53/1.00  fof(f83,plain,(
% 3.53/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f9,axiom,(
% 3.53/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f31,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.53/1.00    inference(ennf_transformation,[],[f9])).
% 3.53/1.00  
% 3.53/1.00  fof(f61,plain,(
% 3.53/1.00    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f31])).
% 3.53/1.00  
% 3.53/1.00  fof(f2,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f18,plain,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.53/1.00    inference(unused_predicate_definition_removal,[],[f2])).
% 3.53/1.00  
% 3.53/1.00  fof(f21,plain,(
% 3.53/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.53/1.00    inference(ennf_transformation,[],[f18])).
% 3.53/1.00  
% 3.53/1.00  fof(f54,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.53/1.00    inference(cnf_transformation,[],[f21])).
% 3.53/1.00  
% 3.53/1.00  fof(f11,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f33,plain,(
% 3.53/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f11])).
% 3.53/1.00  
% 3.53/1.00  fof(f34,plain,(
% 3.53/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f33])).
% 3.53/1.00  
% 3.53/1.00  fof(f64,plain,(
% 3.53/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f34])).
% 3.53/1.00  
% 3.53/1.00  fof(f8,axiom,(
% 3.53/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f29,plain,(
% 3.53/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f8])).
% 3.53/1.00  
% 3.53/1.00  fof(f30,plain,(
% 3.53/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.53/1.00    inference(flattening,[],[f29])).
% 3.53/1.00  
% 3.53/1.00  fof(f60,plain,(
% 3.53/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f30])).
% 3.53/1.00  
% 3.53/1.00  fof(f84,plain,(
% 3.53/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.53/1.00    inference(cnf_transformation,[],[f52])).
% 3.53/1.00  
% 3.53/1.00  fof(f1,axiom,(
% 3.53/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f19,plain,(
% 3.53/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.53/1.00    inference(ennf_transformation,[],[f1])).
% 3.53/1.00  
% 3.53/1.00  fof(f20,plain,(
% 3.53/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.53/1.00    inference(flattening,[],[f19])).
% 3.53/1.00  
% 3.53/1.00  fof(f53,plain,(
% 3.53/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f20])).
% 3.53/1.00  
% 3.53/1.00  fof(f4,axiom,(
% 3.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/1.00  
% 3.53/1.00  fof(f24,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.53/1.00    inference(ennf_transformation,[],[f4])).
% 3.53/1.00  
% 3.53/1.00  fof(f25,plain,(
% 3.53/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.53/1.00    inference(flattening,[],[f24])).
% 3.53/1.00  
% 3.53/1.00  fof(f56,plain,(
% 3.53/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.53/1.00    inference(cnf_transformation,[],[f25])).
% 3.53/1.00  
% 3.53/1.00  cnf(c_26,negated_conjecture,
% 3.53/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_462,negated_conjecture,
% 3.53/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1134,plain,
% 3.53/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_6,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_480,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.53/1.00      | ~ l1_pre_topc(X1_55)
% 3.53/1.00      | l1_pre_topc(X0_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1118,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.53/1.00      | l1_pre_topc(X0_55) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2281,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1134,c_1118]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_33,negated_conjecture,
% 3.53/1.00      ( l1_pre_topc(sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_38,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1957,plain,
% 3.53/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.53/1.00      inference(resolution,[status(thm)],[c_480,c_462]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1958,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1957]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2424,plain,
% 3.53/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2281,c_38,c_1958]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5,plain,
% 3.53/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_481,plain,
% 3.53/1.00      ( l1_struct_0(X0_55) | ~ l1_pre_topc(X0_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1117,plain,
% 3.53/1.00      ( l1_struct_0(X0_55) = iProver_top
% 3.53/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2429,plain,
% 3.53/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2424,c_1117]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4,plain,
% 3.53/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_482,plain,
% 3.53/1.00      ( ~ l1_struct_0(X0_55) | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1116,plain,
% 3.53/1.00      ( u1_struct_0(X0_55) = k2_struct_0(X0_55)
% 3.53/1.00      | l1_struct_0(X0_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2669,plain,
% 3.53/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2429,c_1116]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_12,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.53/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/1.00      | ~ l1_pre_topc(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_476,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.53/1.00      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55)))
% 3.53/1.00      | ~ l1_pre_topc(X1_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1122,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.53/1.00      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3617,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 3.53/1.00      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2669,c_1122]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9095,plain,
% 3.53/1.00      ( m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_3617,c_38,c_1958]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9096,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 3.53/1.00      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_9095]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_18,negated_conjecture,
% 3.53/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.53/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_470,negated_conjecture,
% 3.53/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1128,plain,
% 3.53/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_19,negated_conjecture,
% 3.53/1.00      ( sK5 = sK6 ),
% 3.53/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_469,negated_conjecture,
% 3.53/1.00      ( sK5 = sK6 ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1194,plain,
% 3.53/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1128,c_469]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_15,plain,
% 3.53/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.53/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.53/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.53/1.00      | ~ v3_pre_topc(X6,X0)
% 3.53/1.00      | ~ m1_pre_topc(X4,X5)
% 3.53/1.00      | ~ m1_pre_topc(X4,X0)
% 3.53/1.00      | ~ m1_pre_topc(X0,X5)
% 3.53/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.53/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.53/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.53/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.53/1.00      | ~ r2_hidden(X3,X6)
% 3.53/1.00      | ~ v1_funct_1(X2)
% 3.53/1.00      | v2_struct_0(X5)
% 3.53/1.00      | v2_struct_0(X1)
% 3.53/1.00      | v2_struct_0(X4)
% 3.53/1.00      | v2_struct_0(X0)
% 3.53/1.00      | ~ l1_pre_topc(X5)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X5)
% 3.53/1.00      | ~ v2_pre_topc(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_473,plain,
% 3.53/1.00      ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56)
% 3.53/1.00      | ~ r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56)
% 3.53/1.00      | ~ v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 3.53/1.00      | ~ v3_pre_topc(X2_56,X0_55)
% 3.53/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 3.53/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 3.53/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 3.53/1.00      | ~ r1_tarski(X2_56,u1_struct_0(X2_55))
% 3.53/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(X2_55))
% 3.53/1.00      | ~ m1_subset_1(X1_56,u1_struct_0(X0_55))
% 3.53/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 3.53/1.00      | ~ m1_subset_1(X2_56,k1_zfmisc_1(u1_struct_0(X0_55)))
% 3.53/1.00      | ~ r2_hidden(X1_56,X2_56)
% 3.53/1.00      | ~ v1_funct_1(X0_56)
% 3.53/1.00      | v2_struct_0(X1_55)
% 3.53/1.00      | v2_struct_0(X0_55)
% 3.53/1.00      | v2_struct_0(X3_55)
% 3.53/1.00      | v2_struct_0(X2_55)
% 3.53/1.00      | ~ l1_pre_topc(X1_55)
% 3.53/1.00      | ~ l1_pre_topc(X3_55)
% 3.53/1.00      | ~ v2_pre_topc(X1_55)
% 3.53/1.00      | ~ v2_pre_topc(X3_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1125,plain,
% 3.53/1.00      ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56) = iProver_top
% 3.53/1.00      | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56) != iProver_top
% 3.53/1.00      | v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.53/1.00      | v3_pre_topc(X2_56,X0_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.53/1.00      | r1_tarski(X2_56,u1_struct_0(X2_55)) != iProver_top
% 3.53/1.00      | m1_subset_1(X1_56,u1_struct_0(X2_55)) != iProver_top
% 3.53/1.00      | m1_subset_1(X1_56,u1_struct_0(X0_55)) != iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X2_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 3.53/1.00      | r2_hidden(X1_56,X2_56) != iProver_top
% 3.53/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 3.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 3.53/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.53/1.00      | v2_pre_topc(X3_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2,plain,
% 3.53/1.00      ( m1_subset_1(X0,X1)
% 3.53/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.53/1.00      | ~ r2_hidden(X0,X2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_484,plain,
% 3.53/1.00      ( m1_subset_1(X0_56,X1_56)
% 3.53/1.00      | ~ m1_subset_1(X2_56,k1_zfmisc_1(X1_56))
% 3.53/1.00      | ~ r2_hidden(X0_56,X2_56) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1114,plain,
% 3.53/1.00      ( m1_subset_1(X0_56,X1_56) = iProver_top
% 3.53/1.00      | m1_subset_1(X2_56,k1_zfmisc_1(X1_56)) != iProver_top
% 3.53/1.00      | r2_hidden(X0_56,X2_56) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_14,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.53/1.00      | ~ m1_pre_topc(X2,X0)
% 3.53/1.00      | m1_pre_topc(X2,X1)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_474,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.53/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 3.53/1.00      | m1_pre_topc(X2_55,X1_55)
% 3.53/1.00      | ~ l1_pre_topc(X1_55)
% 3.53/1.00      | ~ v2_pre_topc(X1_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1124,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X2_55,X1_55) = iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.53/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1289,plain,
% 3.53/1.00      ( r1_tmap_1(X0_55,X1_55,X0_56,X1_56) = iProver_top
% 3.53/1.00      | r1_tmap_1(X2_55,X1_55,k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_56),X1_56) != iProver_top
% 3.53/1.00      | v1_funct_2(X0_56,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 3.53/1.00      | v3_pre_topc(X2_56,X0_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 3.53/1.00      | r1_tarski(X2_56,u1_struct_0(X2_55)) != iProver_top
% 3.53/1.00      | m1_subset_1(X1_56,u1_struct_0(X2_55)) != iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 3.53/1.00      | m1_subset_1(X2_56,k1_zfmisc_1(u1_struct_0(X0_55))) != iProver_top
% 3.53/1.00      | r2_hidden(X1_56,X2_56) != iProver_top
% 3.53/1.00      | v1_funct_1(X0_56) != iProver_top
% 3.53/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.53/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.53/1.00      | v2_struct_0(X3_55) = iProver_top
% 3.53/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.53/1.00      | l1_pre_topc(X3_55) != iProver_top
% 3.53/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.53/1.00      | v2_pre_topc(X3_55) != iProver_top ),
% 3.53/1.00      inference(forward_subsumption_resolution,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_1125,c_1114,c_1124]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5511,plain,
% 3.53/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.53/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.53/1.00      | v3_pre_topc(X0_56,sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.53/1.00      | r1_tarski(X0_56,u1_struct_0(sK2)) != iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,X0_56) != iProver_top
% 3.53/1.00      | v1_funct_1(sK4) != iProver_top
% 3.53/1.00      | v2_struct_0(sK0) = iProver_top
% 3.53/1.00      | v2_struct_0(sK2) = iProver_top
% 3.53/1.00      | v2_struct_0(sK1) = iProver_top
% 3.53/1.00      | v2_struct_0(sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1194,c_1289]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_30,negated_conjecture,
% 3.53/1.00      ( l1_pre_topc(sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_458,negated_conjecture,
% 3.53/1.00      ( l1_pre_topc(sK1) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1138,plain,
% 3.53/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2177,plain,
% 3.53/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1138,c_1117]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2349,plain,
% 3.53/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2177,c_1116]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_28,negated_conjecture,
% 3.53/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_460,negated_conjecture,
% 3.53/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1136,plain,
% 3.53/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2282,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1136,c_1118]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1959,plain,
% 3.53/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.53/1.00      inference(resolution,[status(thm)],[c_480,c_460]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1960,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2528,plain,
% 3.53/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_2282,c_38,c_1960]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2533,plain,
% 3.53/1.00      ( l1_struct_0(sK2) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2528,c_1117]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3169,plain,
% 3.53/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2533,c_1116]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5512,plain,
% 3.53/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.53/1.00      | v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
% 3.53/1.00      | v3_pre_topc(X0_56,sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.53/1.00      | r1_tarski(X0_56,k2_struct_0(sK2)) != iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top
% 3.53/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,X0_56) != iProver_top
% 3.53/1.00      | v1_funct_1(sK4) != iProver_top
% 3.53/1.00      | v2_struct_0(sK0) = iProver_top
% 3.53/1.00      | v2_struct_0(sK2) = iProver_top
% 3.53/1.00      | v2_struct_0(sK1) = iProver_top
% 3.53/1.00      | v2_struct_0(sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_5511,c_2349,c_2669,c_3169]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_35,negated_conjecture,
% 3.53/1.00      ( ~ v2_struct_0(sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_36,plain,
% 3.53/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_34,negated_conjecture,
% 3.53/1.00      ( v2_pre_topc(sK0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_37,plain,
% 3.53/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_32,negated_conjecture,
% 3.53/1.00      ( ~ v2_struct_0(sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_39,plain,
% 3.53/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_31,negated_conjecture,
% 3.53/1.00      ( v2_pre_topc(sK1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_40,plain,
% 3.53/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_41,plain,
% 3.53/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_29,negated_conjecture,
% 3.53/1.00      ( ~ v2_struct_0(sK2) ),
% 3.53/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_42,plain,
% 3.53/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_27,negated_conjecture,
% 3.53/1.00      ( ~ v2_struct_0(sK3) ),
% 3.53/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_44,plain,
% 3.53/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_45,plain,
% 3.53/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_25,negated_conjecture,
% 3.53/1.00      ( v1_funct_1(sK4) ),
% 3.53/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_46,plain,
% 3.53/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_17,negated_conjecture,
% 3.53/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.53/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_52,plain,
% 3.53/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_23,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.53/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_465,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1131,plain,
% 3.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3174,plain,
% 3.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2349,c_1131]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3598,plain,
% 3.53/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2669,c_3174]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_24,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_464,negated_conjecture,
% 3.53/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1132,plain,
% 3.53/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3175,plain,
% 3.53/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2349,c_1132]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3599,plain,
% 3.53/1.00      ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2669,c_3175]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_20,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_468,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1129,plain,
% 3.53/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1169,plain,
% 3.53/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_1129,c_469]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3812,plain,
% 3.53/1.00      ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_3169,c_1169]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_13,plain,
% 3.53/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_475,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X0_55) | ~ l1_pre_topc(X0_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1123,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X0_55) = iProver_top
% 3.53/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_10,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.53/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.53/1.00      | ~ l1_pre_topc(X0)
% 3.53/1.00      | ~ l1_pre_topc(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_264,plain,
% 3.53/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.53/1.00      | ~ m1_pre_topc(X0,X1)
% 3.53/1.00      | ~ l1_pre_topc(X1) ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_10,c_6]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_265,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.53/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.53/1.00      | ~ l1_pre_topc(X1) ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_264]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_452,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.53/1.00      | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
% 3.53/1.00      | ~ l1_pre_topc(X1_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_265]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1144,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4639,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK2) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3169,c_1144]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_22,negated_conjecture,
% 3.53/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.53/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_466,negated_conjecture,
% 3.53/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3813,plain,
% 3.53/1.00      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_3169,c_466]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_4690,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK2) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_4639,c_3813]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5036,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK3) = iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK2) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_4690,c_38,c_1960]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5037,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK2) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK3) = iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_5036]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5044,plain,
% 3.53/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1123,c_5037]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5982,plain,
% 3.53/1.00      ( r2_hidden(sK5,X0_56) != iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r1_tarski(X0_56,k2_struct_0(sK2)) != iProver_top
% 3.53/1.00      | v3_pre_topc(X0_56,sK3) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_5512,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_45,
% 3.53/1.00                 c_46,c_52,c_1960,c_3598,c_3599,c_3812,c_5044]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5983,plain,
% 3.53/1.00      ( v3_pre_topc(X0_56,sK3) != iProver_top
% 3.53/1.00      | r1_tarski(X0_56,k2_struct_0(sK2)) != iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,X0_56) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_5982]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9110,plain,
% 3.53/1.00      ( v3_pre_topc(u1_struct_0(X0_55),sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.53/1.00      | r1_tarski(u1_struct_0(X0_55),k2_struct_0(sK2)) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,u1_struct_0(X0_55)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_9096,c_5983]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_8,plain,
% 3.53/1.00      ( m1_pre_topc(X0,X1)
% 3.53/1.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.53/1.00      | ~ l1_pre_topc(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_478,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55)
% 3.53/1.00      | ~ m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
% 3.53/1.00      | ~ l1_pre_topc(X1_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1120,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55) = iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2977,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK2) = iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_466,c_1120]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1,plain,
% 3.53/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_485,plain,
% 3.53/1.00      ( r1_tarski(X0_56,X1_56)
% 3.53/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1113,plain,
% 3.53/1.00      ( r1_tarski(X0_56,X1_56) = iProver_top
% 3.53/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2848,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.53/1.00      | r1_tarski(u1_struct_0(X0_55),u1_struct_0(X1_55)) = iProver_top
% 3.53/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1122,c_1113]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5770,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK2) != iProver_top
% 3.53/1.00      | r1_tarski(u1_struct_0(X0_55),k2_struct_0(sK2)) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_3169,c_2848]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9739,plain,
% 3.53/1.00      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 3.53/1.00      | v3_pre_topc(u1_struct_0(X0_55),sK3) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,u1_struct_0(X0_55)) != iProver_top ),
% 3.53/1.00      inference(global_propositional_subsumption,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_9110,c_38,c_1960,c_2977,c_5770]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9740,plain,
% 3.53/1.00      ( v3_pre_topc(u1_struct_0(X0_55),sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,u1_struct_0(X0_55)) != iProver_top ),
% 3.53/1.00      inference(renaming,[status(thm)],[c_9739]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9749,plain,
% 3.53/1.00      ( v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(sK3,sK3) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2669,c_9740]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_9769,plain,
% 3.53/1.00      ( v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
% 3.53/1.00      | m1_pre_topc(sK3,sK3) != iProver_top
% 3.53/1.00      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(light_normalisation,[status(thm)],[c_9749,c_2669]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_11,plain,
% 3.53/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.53/1.00      | ~ l1_pre_topc(X0)
% 3.53/1.00      | ~ v2_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_477,plain,
% 3.53/1.00      ( v3_pre_topc(k2_struct_0(X0_55),X0_55)
% 3.53/1.00      | ~ l1_pre_topc(X0_55)
% 3.53/1.00      | ~ v2_pre_topc(X0_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5251,plain,
% 3.53/1.00      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.53/1.00      | ~ l1_pre_topc(sK3)
% 3.53/1.00      | ~ v2_pre_topc(sK3) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_477]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_5252,plain,
% 3.53/1.00      ( v3_pre_topc(k2_struct_0(sK3),sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_5251]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_7,plain,
% 3.53/1.00      ( v2_struct_0(X0)
% 3.53/1.00      | ~ l1_struct_0(X0)
% 3.53/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_479,plain,
% 3.53/1.00      ( v2_struct_0(X0_55)
% 3.53/1.00      | ~ l1_struct_0(X0_55)
% 3.53/1.00      | ~ v1_xboole_0(u1_struct_0(X0_55)) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1119,plain,
% 3.53/1.00      ( v2_struct_0(X0_55) = iProver_top
% 3.53/1.00      | l1_struct_0(X0_55) != iProver_top
% 3.53/1.00      | v1_xboole_0(u1_struct_0(X0_55)) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3619,plain,
% 3.53/1.00      ( v2_struct_0(sK3) = iProver_top
% 3.53/1.00      | l1_struct_0(sK3) != iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_2669,c_1119]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_21,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.53/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_467,negated_conjecture,
% 3.53/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1130,plain,
% 3.53/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_0,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.53/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_486,plain,
% 3.53/1.00      ( ~ m1_subset_1(X0_56,X1_56)
% 3.53/1.00      | r2_hidden(X0_56,X1_56)
% 3.53/1.00      | v1_xboole_0(X1_56) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1112,plain,
% 3.53/1.00      ( m1_subset_1(X0_56,X1_56) != iProver_top
% 3.53/1.00      | r2_hidden(X0_56,X1_56) = iProver_top
% 3.53/1.00      | v1_xboole_0(X1_56) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_1773,plain,
% 3.53/1.00      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.53/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.53/1.00      inference(superposition,[status(thm)],[c_1130,c_1112]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3600,plain,
% 3.53/1.00      ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top
% 3.53/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.53/1.00      inference(demodulation,[status(thm)],[c_2669,c_1773]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_3,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.53/1.00      | ~ l1_pre_topc(X1)
% 3.53/1.00      | ~ v2_pre_topc(X1)
% 3.53/1.00      | v2_pre_topc(X0) ),
% 3.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_483,plain,
% 3.53/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.53/1.00      | ~ l1_pre_topc(X1_55)
% 3.53/1.00      | ~ v2_pre_topc(X1_55)
% 3.53/1.00      | v2_pre_topc(X0_55) ),
% 3.53/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2692,plain,
% 3.53/1.00      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 3.53/1.00      inference(resolution,[status(thm)],[c_483,c_462]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2693,plain,
% 3.53/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.53/1.00      | v2_pre_topc(sK3) = iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2692]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2338,plain,
% 3.53/1.00      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_481]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2339,plain,
% 3.53/1.00      ( l1_struct_0(sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2066,plain,
% 3.53/1.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 3.53/1.00      inference(instantiation,[status(thm)],[c_475]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(c_2069,plain,
% 3.53/1.00      ( m1_pre_topc(sK3,sK3) = iProver_top
% 3.53/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2066]) ).
% 3.53/1.00  
% 3.53/1.00  cnf(contradiction,plain,
% 3.53/1.00      ( $false ),
% 3.53/1.00      inference(minisat,
% 3.53/1.00                [status(thm)],
% 3.53/1.00                [c_9769,c_5252,c_3619,c_3600,c_2693,c_2339,c_2069,c_1958,
% 3.53/1.00                 c_44,c_38,c_37]) ).
% 3.53/1.00  
% 3.53/1.00  
% 3.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/1.00  
% 3.53/1.00  ------                               Statistics
% 3.53/1.00  
% 3.53/1.00  ------ Selected
% 3.53/1.00  
% 3.53/1.00  total_time:                             0.395
% 3.53/1.00  
%------------------------------------------------------------------------------
