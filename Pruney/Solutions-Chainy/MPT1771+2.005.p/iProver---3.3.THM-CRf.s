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
% DateTime   : Thu Dec  3 12:23:06 EST 2020

% Result     : Theorem 11.70s
% Output     : CNFRefutation 11.70s
% Verified   : 
% Statistics : Number of formulae       :  201 (3622 expanded)
%              Number of clauses        :  139 ( 696 expanded)
%              Number of leaves         :   18 (1754 expanded)
%              Depth                    :   22
%              Number of atoms          : 1521 (57425 expanded)
%              Number of equality atoms :  403 (5350 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                    & X5 = X6 )
                                 => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                      & X5 = X6 )
                                   => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6)
        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6)
                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                    & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6)
                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                            ( ~ r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6)
                            & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
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

fof(f36,plain,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f27,f35,f34,f33,f32,f31,f30,f29])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
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
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f47])).

fof(f65,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_394,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1551,plain,
    ( X0_51 != X1_51
    | k2_tmap_1(sK0,sK1,sK4,sK2) != X1_51
    | k2_tmap_1(sK0,sK1,sK4,sK2) = X0_51 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_1644,plain,
    ( X0_51 != k2_tmap_1(sK0,sK1,sK4,sK2)
    | k2_tmap_1(sK0,sK1,sK4,sK2) = X0_51
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_31757,plain,
    ( k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) != k2_tmap_1(sK0,sK1,sK4,sK2)
    | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_31758,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) != k2_tmap_1(sK0,sK1,sK4,sK2)
    | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_31757])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_987,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | v1_funct_2(k3_tmap_1(X1_50,sK1,X0_50,X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X1_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_6524,plain,
    ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_6530,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_6524])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_371,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_903,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_374,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_900,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_388,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_887,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_1847,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_887])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2058,plain,
    ( v2_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1847,c_33,c_34,c_35,c_40,c_41])).

cnf(c_2059,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2058])).

cnf(c_2065,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_903,c_2059])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_389,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_886,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_1561,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_886])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1739,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1561,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41])).

cnf(c_1740,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | m1_pre_topc(X0_50,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1739])).

cnf(c_1745,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_903,c_1740])).

cnf(c_2069,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2065,c_1745])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_55,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_57,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_2221,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2069,c_30,c_31,c_32,c_39,c_57])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_369,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_905,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_2066,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_2059])).

cnf(c_1746,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_905,c_1740])).

cnf(c_2068,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2066,c_1746])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2127,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_30,c_31,c_32,c_37,c_57])).

cnf(c_8,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_383,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k3_tmap_1(X2_50,X1_50,X4_50,X3_50,X0_51)),k3_tmap_1(X2_50,X1_50,X4_50,X0_50,X0_51))
    | ~ v1_funct_2(X0_51,u1_struct_0(X4_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X3_50,X4_50)
    | ~ m1_pre_topc(X4_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X4_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_892,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k3_tmap_1(X2_50,X1_50,X4_50,X3_50,X0_51)),k3_tmap_1(X2_50,X1_50,X4_50,X0_50,X0_51)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X4_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X4_50) != iProver_top
    | m1_pre_topc(X4_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_2131,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_892])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3526,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,c_57])).

cnf(c_3527,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_3526])).

cnf(c_3533,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_3527])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3538,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3533,c_38,c_39,c_43])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_387,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_888,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_390,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
    | ~ v1_funct_2(X1_51,X0_52,X1_52)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | X0_51 = X1_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_885,plain,
    ( X0_51 = X1_51
    | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_1935,plain,
    ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51) = X1_51
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),X1_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_885])).

cnf(c_4441,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_1935])).

cnf(c_4469,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4441])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_385,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_989,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X2_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51)) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_3444,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_3446,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_401,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
    | r1_tmap_1(X0_50,X1_50,X2_51,X3_51)
    | X2_51 != X0_51
    | X3_51 != X1_51 ),
    theory(equality)).

cnf(c_1110,plain,
    ( ~ r1_tmap_1(sK2,sK1,X0_51,X1_51)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != X0_51
    | sK6 != X1_51 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_1158,plain,
    ( ~ r1_tmap_1(sK2,sK1,X0_51,sK6)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != X0_51
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1381,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51),sK6)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_2590,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_2592,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_890,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_1566,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_890])).

cnf(c_2051,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1566,c_33,c_34,c_35,c_40,c_41])).

cnf(c_2052,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2051])).

cnf(c_2228,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_2052])).

cnf(c_2240,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2228])).

cnf(c_889,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_2227,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_889])).

cnf(c_2239,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2227])).

cnf(c_2226,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_888])).

cnf(c_2238,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2226])).

cnf(c_2134,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_2052])).

cnf(c_2146,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2134])).

cnf(c_2133,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_889])).

cnf(c_2145,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2133])).

cnf(c_2132,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_888])).

cnf(c_2144,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2132])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_381,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
    | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_984,plain,
    ( ~ r1_tmap_1(X0_50,sK1,X0_51,X1_51)
    | r1_tmap_1(X1_50,sK1,k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X1_50,X0_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X1_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1229,plain,
    ( r1_tmap_1(X0_50,sK1,k3_tmap_1(X1_50,sK1,sK3,X0_50,X0_51),X1_51)
    | ~ r1_tmap_1(sK3,sK1,X0_51,X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X0_50,sK3)
    | ~ m1_pre_topc(sK3,X1_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_1330,plain,
    ( ~ r1_tmap_1(sK3,sK1,X0_51,X1_51)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_1380,plain,
    ( ~ r1_tmap_1(sK3,sK1,X0_51,sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51),sK6)
    | ~ v1_funct_2(X0_51,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_1750,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK2,X0_50)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_1752,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_393,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1698,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_1348,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_379,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_896,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_13,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_378,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_914,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_896,c_378])).

cnf(c_933,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_914])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_376,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_898,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_913,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_898,c_378])).

cnf(c_918,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_913])).

cnf(c_56,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31758,c_6530,c_4469,c_3446,c_2592,c_2240,c_2239,c_2238,c_2146,c_2145,c_2144,c_1752,c_1698,c_1348,c_933,c_918,c_56,c_11,c_14,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.70/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.70/1.99  
% 11.70/1.99  ------  iProver source info
% 11.70/1.99  
% 11.70/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.70/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.70/1.99  git: non_committed_changes: false
% 11.70/1.99  git: last_make_outside_of_git: false
% 11.70/1.99  
% 11.70/1.99  ------ 
% 11.70/1.99  
% 11.70/1.99  ------ Input Options
% 11.70/1.99  
% 11.70/1.99  --out_options                           all
% 11.70/1.99  --tptp_safe_out                         true
% 11.70/1.99  --problem_path                          ""
% 11.70/1.99  --include_path                          ""
% 11.70/1.99  --clausifier                            res/vclausify_rel
% 11.70/1.99  --clausifier_options                    ""
% 11.70/1.99  --stdin                                 false
% 11.70/1.99  --stats_out                             all
% 11.70/1.99  
% 11.70/1.99  ------ General Options
% 11.70/1.99  
% 11.70/1.99  --fof                                   false
% 11.70/1.99  --time_out_real                         305.
% 11.70/1.99  --time_out_virtual                      -1.
% 11.70/1.99  --symbol_type_check                     false
% 11.70/1.99  --clausify_out                          false
% 11.70/1.99  --sig_cnt_out                           false
% 11.70/1.99  --trig_cnt_out                          false
% 11.70/1.99  --trig_cnt_out_tolerance                1.
% 11.70/1.99  --trig_cnt_out_sk_spl                   false
% 11.70/1.99  --abstr_cl_out                          false
% 11.70/1.99  
% 11.70/1.99  ------ Global Options
% 11.70/1.99  
% 11.70/1.99  --schedule                              default
% 11.70/1.99  --add_important_lit                     false
% 11.70/1.99  --prop_solver_per_cl                    1000
% 11.70/1.99  --min_unsat_core                        false
% 11.70/1.99  --soft_assumptions                      false
% 11.70/1.99  --soft_lemma_size                       3
% 11.70/1.99  --prop_impl_unit_size                   0
% 11.70/1.99  --prop_impl_unit                        []
% 11.70/1.99  --share_sel_clauses                     true
% 11.70/1.99  --reset_solvers                         false
% 11.70/1.99  --bc_imp_inh                            [conj_cone]
% 11.70/1.99  --conj_cone_tolerance                   3.
% 11.70/1.99  --extra_neg_conj                        none
% 11.70/1.99  --large_theory_mode                     true
% 11.70/1.99  --prolific_symb_bound                   200
% 11.70/1.99  --lt_threshold                          2000
% 11.70/1.99  --clause_weak_htbl                      true
% 11.70/1.99  --gc_record_bc_elim                     false
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing Options
% 11.70/1.99  
% 11.70/1.99  --preprocessing_flag                    true
% 11.70/1.99  --time_out_prep_mult                    0.1
% 11.70/1.99  --splitting_mode                        input
% 11.70/1.99  --splitting_grd                         true
% 11.70/1.99  --splitting_cvd                         false
% 11.70/1.99  --splitting_cvd_svl                     false
% 11.70/1.99  --splitting_nvd                         32
% 11.70/1.99  --sub_typing                            true
% 11.70/1.99  --prep_gs_sim                           true
% 11.70/1.99  --prep_unflatten                        true
% 11.70/1.99  --prep_res_sim                          true
% 11.70/1.99  --prep_upred                            true
% 11.70/1.99  --prep_sem_filter                       exhaustive
% 11.70/1.99  --prep_sem_filter_out                   false
% 11.70/1.99  --pred_elim                             true
% 11.70/1.99  --res_sim_input                         true
% 11.70/1.99  --eq_ax_congr_red                       true
% 11.70/1.99  --pure_diseq_elim                       true
% 11.70/1.99  --brand_transform                       false
% 11.70/1.99  --non_eq_to_eq                          false
% 11.70/1.99  --prep_def_merge                        true
% 11.70/1.99  --prep_def_merge_prop_impl              false
% 11.70/1.99  --prep_def_merge_mbd                    true
% 11.70/1.99  --prep_def_merge_tr_red                 false
% 11.70/1.99  --prep_def_merge_tr_cl                  false
% 11.70/1.99  --smt_preprocessing                     true
% 11.70/1.99  --smt_ac_axioms                         fast
% 11.70/1.99  --preprocessed_out                      false
% 11.70/1.99  --preprocessed_stats                    false
% 11.70/1.99  
% 11.70/1.99  ------ Abstraction refinement Options
% 11.70/1.99  
% 11.70/1.99  --abstr_ref                             []
% 11.70/1.99  --abstr_ref_prep                        false
% 11.70/1.99  --abstr_ref_until_sat                   false
% 11.70/1.99  --abstr_ref_sig_restrict                funpre
% 11.70/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.70/1.99  --abstr_ref_under                       []
% 11.70/1.99  
% 11.70/1.99  ------ SAT Options
% 11.70/1.99  
% 11.70/1.99  --sat_mode                              false
% 11.70/1.99  --sat_fm_restart_options                ""
% 11.70/1.99  --sat_gr_def                            false
% 11.70/1.99  --sat_epr_types                         true
% 11.70/1.99  --sat_non_cyclic_types                  false
% 11.70/1.99  --sat_finite_models                     false
% 11.70/1.99  --sat_fm_lemmas                         false
% 11.70/1.99  --sat_fm_prep                           false
% 11.70/1.99  --sat_fm_uc_incr                        true
% 11.70/1.99  --sat_out_model                         small
% 11.70/1.99  --sat_out_clauses                       false
% 11.70/1.99  
% 11.70/1.99  ------ QBF Options
% 11.70/1.99  
% 11.70/1.99  --qbf_mode                              false
% 11.70/1.99  --qbf_elim_univ                         false
% 11.70/1.99  --qbf_dom_inst                          none
% 11.70/1.99  --qbf_dom_pre_inst                      false
% 11.70/1.99  --qbf_sk_in                             false
% 11.70/1.99  --qbf_pred_elim                         true
% 11.70/1.99  --qbf_split                             512
% 11.70/1.99  
% 11.70/1.99  ------ BMC1 Options
% 11.70/1.99  
% 11.70/1.99  --bmc1_incremental                      false
% 11.70/1.99  --bmc1_axioms                           reachable_all
% 11.70/1.99  --bmc1_min_bound                        0
% 11.70/1.99  --bmc1_max_bound                        -1
% 11.70/1.99  --bmc1_max_bound_default                -1
% 11.70/1.99  --bmc1_symbol_reachability              true
% 11.70/1.99  --bmc1_property_lemmas                  false
% 11.70/1.99  --bmc1_k_induction                      false
% 11.70/1.99  --bmc1_non_equiv_states                 false
% 11.70/1.99  --bmc1_deadlock                         false
% 11.70/1.99  --bmc1_ucm                              false
% 11.70/1.99  --bmc1_add_unsat_core                   none
% 11.70/1.99  --bmc1_unsat_core_children              false
% 11.70/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.70/1.99  --bmc1_out_stat                         full
% 11.70/1.99  --bmc1_ground_init                      false
% 11.70/1.99  --bmc1_pre_inst_next_state              false
% 11.70/1.99  --bmc1_pre_inst_state                   false
% 11.70/1.99  --bmc1_pre_inst_reach_state             false
% 11.70/1.99  --bmc1_out_unsat_core                   false
% 11.70/1.99  --bmc1_aig_witness_out                  false
% 11.70/1.99  --bmc1_verbose                          false
% 11.70/1.99  --bmc1_dump_clauses_tptp                false
% 11.70/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.70/1.99  --bmc1_dump_file                        -
% 11.70/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.70/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.70/1.99  --bmc1_ucm_extend_mode                  1
% 11.70/1.99  --bmc1_ucm_init_mode                    2
% 11.70/1.99  --bmc1_ucm_cone_mode                    none
% 11.70/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.70/1.99  --bmc1_ucm_relax_model                  4
% 11.70/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.70/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.70/1.99  --bmc1_ucm_layered_model                none
% 11.70/1.99  --bmc1_ucm_max_lemma_size               10
% 11.70/1.99  
% 11.70/1.99  ------ AIG Options
% 11.70/1.99  
% 11.70/1.99  --aig_mode                              false
% 11.70/1.99  
% 11.70/1.99  ------ Instantiation Options
% 11.70/1.99  
% 11.70/1.99  --instantiation_flag                    true
% 11.70/1.99  --inst_sos_flag                         true
% 11.70/1.99  --inst_sos_phase                        true
% 11.70/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.70/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.70/1.99  --inst_lit_sel_side                     num_symb
% 11.70/1.99  --inst_solver_per_active                1400
% 11.70/1.99  --inst_solver_calls_frac                1.
% 11.70/1.99  --inst_passive_queue_type               priority_queues
% 11.70/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.70/1.99  --inst_passive_queues_freq              [25;2]
% 11.70/1.99  --inst_dismatching                      true
% 11.70/1.99  --inst_eager_unprocessed_to_passive     true
% 11.70/1.99  --inst_prop_sim_given                   true
% 11.70/1.99  --inst_prop_sim_new                     false
% 11.70/1.99  --inst_subs_new                         false
% 11.70/1.99  --inst_eq_res_simp                      false
% 11.70/1.99  --inst_subs_given                       false
% 11.70/1.99  --inst_orphan_elimination               true
% 11.70/1.99  --inst_learning_loop_flag               true
% 11.70/1.99  --inst_learning_start                   3000
% 11.70/1.99  --inst_learning_factor                  2
% 11.70/1.99  --inst_start_prop_sim_after_learn       3
% 11.70/1.99  --inst_sel_renew                        solver
% 11.70/1.99  --inst_lit_activity_flag                true
% 11.70/1.99  --inst_restr_to_given                   false
% 11.70/1.99  --inst_activity_threshold               500
% 11.70/1.99  --inst_out_proof                        true
% 11.70/1.99  
% 11.70/1.99  ------ Resolution Options
% 11.70/1.99  
% 11.70/1.99  --resolution_flag                       true
% 11.70/1.99  --res_lit_sel                           adaptive
% 11.70/1.99  --res_lit_sel_side                      none
% 11.70/1.99  --res_ordering                          kbo
% 11.70/1.99  --res_to_prop_solver                    active
% 11.70/1.99  --res_prop_simpl_new                    false
% 11.70/1.99  --res_prop_simpl_given                  true
% 11.70/1.99  --res_passive_queue_type                priority_queues
% 11.70/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.70/1.99  --res_passive_queues_freq               [15;5]
% 11.70/1.99  --res_forward_subs                      full
% 11.70/1.99  --res_backward_subs                     full
% 11.70/1.99  --res_forward_subs_resolution           true
% 11.70/1.99  --res_backward_subs_resolution          true
% 11.70/1.99  --res_orphan_elimination                true
% 11.70/1.99  --res_time_limit                        2.
% 11.70/1.99  --res_out_proof                         true
% 11.70/1.99  
% 11.70/1.99  ------ Superposition Options
% 11.70/1.99  
% 11.70/1.99  --superposition_flag                    true
% 11.70/1.99  --sup_passive_queue_type                priority_queues
% 11.70/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.70/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.70/1.99  --demod_completeness_check              fast
% 11.70/1.99  --demod_use_ground                      true
% 11.70/1.99  --sup_to_prop_solver                    passive
% 11.70/1.99  --sup_prop_simpl_new                    true
% 11.70/1.99  --sup_prop_simpl_given                  true
% 11.70/1.99  --sup_fun_splitting                     true
% 11.70/1.99  --sup_smt_interval                      50000
% 11.70/1.99  
% 11.70/1.99  ------ Superposition Simplification Setup
% 11.70/1.99  
% 11.70/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.70/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.70/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.70/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.70/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.70/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.70/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.70/1.99  --sup_immed_triv                        [TrivRules]
% 11.70/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.70/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.70/1.99  --sup_immed_bw_main                     []
% 11.70/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.70/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.70/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.70/1.99  --sup_input_bw                          []
% 11.70/1.99  
% 11.70/1.99  ------ Combination Options
% 11.70/1.99  
% 11.70/1.99  --comb_res_mult                         3
% 11.70/1.99  --comb_sup_mult                         2
% 11.70/1.99  --comb_inst_mult                        10
% 11.70/1.99  
% 11.70/1.99  ------ Debug Options
% 11.70/1.99  
% 11.70/1.99  --dbg_backtrace                         false
% 11.70/1.99  --dbg_dump_prop_clauses                 false
% 11.70/1.99  --dbg_dump_prop_clauses_file            -
% 11.70/1.99  --dbg_out_stat                          false
% 11.70/1.99  ------ Parsing...
% 11.70/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.70/1.99  ------ Proving...
% 11.70/1.99  ------ Problem Properties 
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  clauses                                 30
% 11.70/1.99  conjectures                             19
% 11.70/1.99  EPR                                     15
% 11.70/1.99  Horn                                    23
% 11.70/1.99  unary                                   19
% 11.70/1.99  binary                                  1
% 11.70/1.99  lits                                    134
% 11.70/1.99  lits eq                                 4
% 11.70/1.99  fd_pure                                 0
% 11.70/1.99  fd_pseudo                               0
% 11.70/1.99  fd_cond                                 0
% 11.70/1.99  fd_pseudo_cond                          1
% 11.70/1.99  AC symbols                              0
% 11.70/1.99  
% 11.70/1.99  ------ Schedule dynamic 5 is on 
% 11.70/1.99  
% 11.70/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  ------ 
% 11.70/1.99  Current options:
% 11.70/1.99  ------ 
% 11.70/1.99  
% 11.70/1.99  ------ Input Options
% 11.70/1.99  
% 11.70/1.99  --out_options                           all
% 11.70/1.99  --tptp_safe_out                         true
% 11.70/1.99  --problem_path                          ""
% 11.70/1.99  --include_path                          ""
% 11.70/1.99  --clausifier                            res/vclausify_rel
% 11.70/1.99  --clausifier_options                    ""
% 11.70/1.99  --stdin                                 false
% 11.70/1.99  --stats_out                             all
% 11.70/1.99  
% 11.70/1.99  ------ General Options
% 11.70/1.99  
% 11.70/1.99  --fof                                   false
% 11.70/1.99  --time_out_real                         305.
% 11.70/1.99  --time_out_virtual                      -1.
% 11.70/1.99  --symbol_type_check                     false
% 11.70/1.99  --clausify_out                          false
% 11.70/1.99  --sig_cnt_out                           false
% 11.70/1.99  --trig_cnt_out                          false
% 11.70/1.99  --trig_cnt_out_tolerance                1.
% 11.70/1.99  --trig_cnt_out_sk_spl                   false
% 11.70/1.99  --abstr_cl_out                          false
% 11.70/1.99  
% 11.70/1.99  ------ Global Options
% 11.70/1.99  
% 11.70/1.99  --schedule                              default
% 11.70/1.99  --add_important_lit                     false
% 11.70/1.99  --prop_solver_per_cl                    1000
% 11.70/1.99  --min_unsat_core                        false
% 11.70/1.99  --soft_assumptions                      false
% 11.70/1.99  --soft_lemma_size                       3
% 11.70/1.99  --prop_impl_unit_size                   0
% 11.70/1.99  --prop_impl_unit                        []
% 11.70/1.99  --share_sel_clauses                     true
% 11.70/1.99  --reset_solvers                         false
% 11.70/1.99  --bc_imp_inh                            [conj_cone]
% 11.70/1.99  --conj_cone_tolerance                   3.
% 11.70/1.99  --extra_neg_conj                        none
% 11.70/1.99  --large_theory_mode                     true
% 11.70/1.99  --prolific_symb_bound                   200
% 11.70/1.99  --lt_threshold                          2000
% 11.70/1.99  --clause_weak_htbl                      true
% 11.70/1.99  --gc_record_bc_elim                     false
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing Options
% 11.70/1.99  
% 11.70/1.99  --preprocessing_flag                    true
% 11.70/1.99  --time_out_prep_mult                    0.1
% 11.70/1.99  --splitting_mode                        input
% 11.70/1.99  --splitting_grd                         true
% 11.70/1.99  --splitting_cvd                         false
% 11.70/1.99  --splitting_cvd_svl                     false
% 11.70/1.99  --splitting_nvd                         32
% 11.70/1.99  --sub_typing                            true
% 11.70/1.99  --prep_gs_sim                           true
% 11.70/1.99  --prep_unflatten                        true
% 11.70/1.99  --prep_res_sim                          true
% 11.70/1.99  --prep_upred                            true
% 11.70/1.99  --prep_sem_filter                       exhaustive
% 11.70/1.99  --prep_sem_filter_out                   false
% 11.70/1.99  --pred_elim                             true
% 11.70/1.99  --res_sim_input                         true
% 11.70/1.99  --eq_ax_congr_red                       true
% 11.70/1.99  --pure_diseq_elim                       true
% 11.70/1.99  --brand_transform                       false
% 11.70/1.99  --non_eq_to_eq                          false
% 11.70/1.99  --prep_def_merge                        true
% 11.70/1.99  --prep_def_merge_prop_impl              false
% 11.70/1.99  --prep_def_merge_mbd                    true
% 11.70/1.99  --prep_def_merge_tr_red                 false
% 11.70/1.99  --prep_def_merge_tr_cl                  false
% 11.70/1.99  --smt_preprocessing                     true
% 11.70/1.99  --smt_ac_axioms                         fast
% 11.70/1.99  --preprocessed_out                      false
% 11.70/1.99  --preprocessed_stats                    false
% 11.70/1.99  
% 11.70/1.99  ------ Abstraction refinement Options
% 11.70/1.99  
% 11.70/1.99  --abstr_ref                             []
% 11.70/1.99  --abstr_ref_prep                        false
% 11.70/1.99  --abstr_ref_until_sat                   false
% 11.70/1.99  --abstr_ref_sig_restrict                funpre
% 11.70/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.70/1.99  --abstr_ref_under                       []
% 11.70/1.99  
% 11.70/1.99  ------ SAT Options
% 11.70/1.99  
% 11.70/1.99  --sat_mode                              false
% 11.70/1.99  --sat_fm_restart_options                ""
% 11.70/1.99  --sat_gr_def                            false
% 11.70/1.99  --sat_epr_types                         true
% 11.70/1.99  --sat_non_cyclic_types                  false
% 11.70/1.99  --sat_finite_models                     false
% 11.70/1.99  --sat_fm_lemmas                         false
% 11.70/1.99  --sat_fm_prep                           false
% 11.70/1.99  --sat_fm_uc_incr                        true
% 11.70/1.99  --sat_out_model                         small
% 11.70/1.99  --sat_out_clauses                       false
% 11.70/1.99  
% 11.70/1.99  ------ QBF Options
% 11.70/1.99  
% 11.70/1.99  --qbf_mode                              false
% 11.70/1.99  --qbf_elim_univ                         false
% 11.70/1.99  --qbf_dom_inst                          none
% 11.70/1.99  --qbf_dom_pre_inst                      false
% 11.70/1.99  --qbf_sk_in                             false
% 11.70/1.99  --qbf_pred_elim                         true
% 11.70/1.99  --qbf_split                             512
% 11.70/1.99  
% 11.70/1.99  ------ BMC1 Options
% 11.70/1.99  
% 11.70/1.99  --bmc1_incremental                      false
% 11.70/1.99  --bmc1_axioms                           reachable_all
% 11.70/1.99  --bmc1_min_bound                        0
% 11.70/1.99  --bmc1_max_bound                        -1
% 11.70/1.99  --bmc1_max_bound_default                -1
% 11.70/1.99  --bmc1_symbol_reachability              true
% 11.70/1.99  --bmc1_property_lemmas                  false
% 11.70/1.99  --bmc1_k_induction                      false
% 11.70/1.99  --bmc1_non_equiv_states                 false
% 11.70/1.99  --bmc1_deadlock                         false
% 11.70/1.99  --bmc1_ucm                              false
% 11.70/1.99  --bmc1_add_unsat_core                   none
% 11.70/1.99  --bmc1_unsat_core_children              false
% 11.70/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.70/1.99  --bmc1_out_stat                         full
% 11.70/1.99  --bmc1_ground_init                      false
% 11.70/1.99  --bmc1_pre_inst_next_state              false
% 11.70/1.99  --bmc1_pre_inst_state                   false
% 11.70/1.99  --bmc1_pre_inst_reach_state             false
% 11.70/1.99  --bmc1_out_unsat_core                   false
% 11.70/1.99  --bmc1_aig_witness_out                  false
% 11.70/1.99  --bmc1_verbose                          false
% 11.70/1.99  --bmc1_dump_clauses_tptp                false
% 11.70/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.70/1.99  --bmc1_dump_file                        -
% 11.70/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.70/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.70/1.99  --bmc1_ucm_extend_mode                  1
% 11.70/1.99  --bmc1_ucm_init_mode                    2
% 11.70/1.99  --bmc1_ucm_cone_mode                    none
% 11.70/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.70/1.99  --bmc1_ucm_relax_model                  4
% 11.70/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.70/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.70/1.99  --bmc1_ucm_layered_model                none
% 11.70/1.99  --bmc1_ucm_max_lemma_size               10
% 11.70/1.99  
% 11.70/1.99  ------ AIG Options
% 11.70/1.99  
% 11.70/1.99  --aig_mode                              false
% 11.70/1.99  
% 11.70/1.99  ------ Instantiation Options
% 11.70/1.99  
% 11.70/1.99  --instantiation_flag                    true
% 11.70/1.99  --inst_sos_flag                         true
% 11.70/1.99  --inst_sos_phase                        true
% 11.70/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.70/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.70/1.99  --inst_lit_sel_side                     none
% 11.70/1.99  --inst_solver_per_active                1400
% 11.70/1.99  --inst_solver_calls_frac                1.
% 11.70/1.99  --inst_passive_queue_type               priority_queues
% 11.70/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.70/1.99  --inst_passive_queues_freq              [25;2]
% 11.70/1.99  --inst_dismatching                      true
% 11.70/1.99  --inst_eager_unprocessed_to_passive     true
% 11.70/1.99  --inst_prop_sim_given                   true
% 11.70/1.99  --inst_prop_sim_new                     false
% 11.70/1.99  --inst_subs_new                         false
% 11.70/1.99  --inst_eq_res_simp                      false
% 11.70/1.99  --inst_subs_given                       false
% 11.70/1.99  --inst_orphan_elimination               true
% 11.70/1.99  --inst_learning_loop_flag               true
% 11.70/1.99  --inst_learning_start                   3000
% 11.70/1.99  --inst_learning_factor                  2
% 11.70/1.99  --inst_start_prop_sim_after_learn       3
% 11.70/1.99  --inst_sel_renew                        solver
% 11.70/1.99  --inst_lit_activity_flag                true
% 11.70/1.99  --inst_restr_to_given                   false
% 11.70/1.99  --inst_activity_threshold               500
% 11.70/1.99  --inst_out_proof                        true
% 11.70/1.99  
% 11.70/1.99  ------ Resolution Options
% 11.70/1.99  
% 11.70/1.99  --resolution_flag                       false
% 11.70/1.99  --res_lit_sel                           adaptive
% 11.70/1.99  --res_lit_sel_side                      none
% 11.70/1.99  --res_ordering                          kbo
% 11.70/1.99  --res_to_prop_solver                    active
% 11.70/1.99  --res_prop_simpl_new                    false
% 11.70/1.99  --res_prop_simpl_given                  true
% 11.70/1.99  --res_passive_queue_type                priority_queues
% 11.70/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.70/1.99  --res_passive_queues_freq               [15;5]
% 11.70/1.99  --res_forward_subs                      full
% 11.70/1.99  --res_backward_subs                     full
% 11.70/1.99  --res_forward_subs_resolution           true
% 11.70/1.99  --res_backward_subs_resolution          true
% 11.70/1.99  --res_orphan_elimination                true
% 11.70/1.99  --res_time_limit                        2.
% 11.70/1.99  --res_out_proof                         true
% 11.70/1.99  
% 11.70/1.99  ------ Superposition Options
% 11.70/1.99  
% 11.70/1.99  --superposition_flag                    true
% 11.70/1.99  --sup_passive_queue_type                priority_queues
% 11.70/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.70/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.70/1.99  --demod_completeness_check              fast
% 11.70/1.99  --demod_use_ground                      true
% 11.70/1.99  --sup_to_prop_solver                    passive
% 11.70/1.99  --sup_prop_simpl_new                    true
% 11.70/1.99  --sup_prop_simpl_given                  true
% 11.70/1.99  --sup_fun_splitting                     true
% 11.70/1.99  --sup_smt_interval                      50000
% 11.70/1.99  
% 11.70/1.99  ------ Superposition Simplification Setup
% 11.70/1.99  
% 11.70/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.70/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.70/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.70/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.70/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.70/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.70/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.70/1.99  --sup_immed_triv                        [TrivRules]
% 11.70/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.70/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.70/1.99  --sup_immed_bw_main                     []
% 11.70/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.70/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.70/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.70/1.99  --sup_input_bw                          []
% 11.70/1.99  
% 11.70/1.99  ------ Combination Options
% 11.70/1.99  
% 11.70/1.99  --comb_res_mult                         3
% 11.70/1.99  --comb_sup_mult                         2
% 11.70/1.99  --comb_inst_mult                        10
% 11.70/1.99  
% 11.70/1.99  ------ Debug Options
% 11.70/1.99  
% 11.70/1.99  --dbg_backtrace                         false
% 11.70/1.99  --dbg_dump_prop_clauses                 false
% 11.70/1.99  --dbg_dump_prop_clauses_file            -
% 11.70/1.99  --dbg_out_stat                          false
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  ------ Proving...
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  % SZS status Theorem for theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  fof(f4,axiom,(
% 11.70/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f17,plain,(
% 11.70/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f4])).
% 11.70/1.99  
% 11.70/1.99  fof(f18,plain,(
% 11.70/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f17])).
% 11.70/1.99  
% 11.70/1.99  fof(f42,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f18])).
% 11.70/1.99  
% 11.70/1.99  fof(f9,conjecture,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f10,negated_conjecture,(
% 11.70/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 11.70/1.99    inference(negated_conjecture,[],[f9])).
% 11.70/1.99  
% 11.70/1.99  fof(f26,plain,(
% 11.70/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f10])).
% 11.70/1.99  
% 11.70/1.99  fof(f27,plain,(
% 11.70/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f26])).
% 11.70/1.99  
% 11.70/1.99  fof(f35,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f34,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f33,plain,(
% 11.70/1.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f32,plain,(
% 11.70/1.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f31,plain,(
% 11.70/1.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f30,plain,(
% 11.70/1.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f29,plain,(
% 11.70/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 11.70/1.99    introduced(choice_axiom,[])).
% 11.70/1.99  
% 11.70/1.99  fof(f36,plain,(
% 11.70/1.99    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 11.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f27,f35,f34,f33,f32,f31,f30,f29])).
% 11.70/1.99  
% 11.70/1.99  fof(f57,plain,(
% 11.70/1.99    m1_pre_topc(sK3,sK0)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f60,plain,(
% 11.70/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f3,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f15,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f3])).
% 11.70/1.99  
% 11.70/1.99  fof(f16,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f15])).
% 11.70/1.99  
% 11.70/1.99  fof(f40,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f16])).
% 11.70/1.99  
% 11.70/1.99  fof(f51,plain,(
% 11.70/1.99    ~v2_struct_0(sK1)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f52,plain,(
% 11.70/1.99    v2_pre_topc(sK1)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f53,plain,(
% 11.70/1.99    l1_pre_topc(sK1)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f58,plain,(
% 11.70/1.99    v1_funct_1(sK4)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f59,plain,(
% 11.70/1.99    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f2,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f13,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f2])).
% 11.70/1.99  
% 11.70/1.99  fof(f14,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f13])).
% 11.70/1.99  
% 11.70/1.99  fof(f39,plain,(
% 11.70/1.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f14])).
% 11.70/1.99  
% 11.70/1.99  fof(f48,plain,(
% 11.70/1.99    ~v2_struct_0(sK0)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f49,plain,(
% 11.70/1.99    v2_pre_topc(sK0)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f50,plain,(
% 11.70/1.99    l1_pre_topc(sK0)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f5,axiom,(
% 11.70/1.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f19,plain,(
% 11.70/1.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.70/1.99    inference(ennf_transformation,[],[f5])).
% 11.70/1.99  
% 11.70/1.99  fof(f44,plain,(
% 11.70/1.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f19])).
% 11.70/1.99  
% 11.70/1.99  fof(f55,plain,(
% 11.70/1.99    m1_pre_topc(sK2,sK0)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f6,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f20,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f6])).
% 11.70/1.99  
% 11.70/1.99  fof(f21,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f20])).
% 11.70/1.99  
% 11.70/1.99  fof(f45,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f21])).
% 11.70/1.99  
% 11.70/1.99  fof(f54,plain,(
% 11.70/1.99    ~v2_struct_0(sK2)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f56,plain,(
% 11.70/1.99    ~v2_struct_0(sK3)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f61,plain,(
% 11.70/1.99    m1_pre_topc(sK2,sK3)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f43,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f18])).
% 11.70/1.99  
% 11.70/1.99  fof(f1,axiom,(
% 11.70/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f11,plain,(
% 11.70/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.70/1.99    inference(ennf_transformation,[],[f1])).
% 11.70/1.99  
% 11.70/1.99  fof(f12,plain,(
% 11.70/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.70/1.99    inference(flattening,[],[f11])).
% 11.70/1.99  
% 11.70/1.99  fof(f28,plain,(
% 11.70/1.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.70/1.99    inference(nnf_transformation,[],[f12])).
% 11.70/1.99  
% 11.70/1.99  fof(f37,plain,(
% 11.70/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f28])).
% 11.70/1.99  
% 11.70/1.99  fof(f41,plain,(
% 11.70/1.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f18])).
% 11.70/1.99  
% 11.70/1.99  fof(f8,axiom,(
% 11.70/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 11.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.70/1.99  
% 11.70/1.99  fof(f24,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.70/1.99    inference(ennf_transformation,[],[f8])).
% 11.70/1.99  
% 11.70/1.99  fof(f25,plain,(
% 11.70/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.70/1.99    inference(flattening,[],[f24])).
% 11.70/1.99  
% 11.70/1.99  fof(f47,plain,(
% 11.70/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(cnf_transformation,[],[f25])).
% 11.70/1.99  
% 11.70/1.99  fof(f68,plain,(
% 11.70/1.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.70/1.99    inference(equality_resolution,[],[f47])).
% 11.70/1.99  
% 11.70/1.99  fof(f65,plain,(
% 11.70/1.99    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f64,plain,(
% 11.70/1.99    sK5 = sK6),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f62,plain,(
% 11.70/1.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f66,plain,(
% 11.70/1.99    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  fof(f63,plain,(
% 11.70/1.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 11.70/1.99    inference(cnf_transformation,[],[f36])).
% 11.70/1.99  
% 11.70/1.99  cnf(c_394,plain,
% 11.70/1.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 11.70/1.99      theory(equality) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1551,plain,
% 11.70/1.99      ( X0_51 != X1_51
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != X1_51
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) = X0_51 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_394]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1644,plain,
% 11.70/1.99      ( X0_51 != k2_tmap_1(sK0,sK1,sK4,sK2)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) = X0_51
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1551]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_31757,plain,
% 11.70/1.99      ( k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) != k2_tmap_1(sK0,sK1,sK4,sK2)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1644]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_31758,plain,
% 11.70/1.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) != k2_tmap_1(sK0,sK1,sK4,sK2)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_31757]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_5,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.70/1.99      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 11.70/1.99      | ~ m1_pre_topc(X4,X3)
% 11.70/1.99      | ~ m1_pre_topc(X1,X3)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.70/1.99      | v2_struct_0(X3)
% 11.70/1.99      | v2_struct_0(X2)
% 11.70/1.99      | ~ v2_pre_topc(X2)
% 11.70/1.99      | ~ v2_pre_topc(X3)
% 11.70/1.99      | ~ l1_pre_topc(X2)
% 11.70/1.99      | ~ l1_pre_topc(X3)
% 11.70/1.99      | ~ v1_funct_1(X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_386,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.70/1.99      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X3_50,X2_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X2_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X2_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X2_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X2_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_987,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 11.70/1.99      | v1_funct_2(k3_tmap_1(X1_50,sK1,X0_50,X2_50,X0_51),u1_struct_0(X2_50),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X1_50)
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X1_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_386]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_6524,plain,
% 11.70/1.99      ( v1_funct_2(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.70/1.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,X0_50)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(X0_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X0_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_987]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_6530,plain,
% 11.70/1.99      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.70/1.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_6524]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_20,negated_conjecture,
% 11.70/1.99      ( m1_pre_topc(sK3,sK0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_371,negated_conjecture,
% 11.70/1.99      ( m1_pre_topc(sK3,sK0) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_20]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_903,plain,
% 11.70/1.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_17,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 11.70/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_374,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_17]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_900,plain,
% 11.70/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.70/1.99      | ~ m1_pre_topc(X3,X4)
% 11.70/1.99      | ~ m1_pre_topc(X3,X1)
% 11.70/1.99      | ~ m1_pre_topc(X1,X4)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.70/1.99      | v2_struct_0(X4)
% 11.70/1.99      | v2_struct_0(X2)
% 11.70/1.99      | ~ v2_pre_topc(X2)
% 11.70/1.99      | ~ v2_pre_topc(X4)
% 11.70/1.99      | ~ l1_pre_topc(X2)
% 11.70/1.99      | ~ l1_pre_topc(X4)
% 11.70/1.99      | ~ v1_funct_1(X0)
% 11.70/1.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_388,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X3_50)
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X3_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X3_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X3_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X3_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51)
% 11.70/1.99      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_887,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
% 11.70/1.99      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X3_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X3_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X3_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1847,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 11.70/1.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,X1_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_900,c_887]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_26,negated_conjecture,
% 11.70/1.99      ( ~ v2_struct_0(sK1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_33,plain,
% 11.70/1.99      ( v2_struct_0(sK1) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_25,negated_conjecture,
% 11.70/1.99      ( v2_pre_topc(sK1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_34,plain,
% 11.70/1.99      ( v2_pre_topc(sK1) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_24,negated_conjecture,
% 11.70/1.99      ( l1_pre_topc(sK1) ),
% 11.70/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_35,plain,
% 11.70/1.99      ( l1_pre_topc(sK1) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_19,negated_conjecture,
% 11.70/1.99      ( v1_funct_1(sK4) ),
% 11.70/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_40,plain,
% 11.70/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_18,negated_conjecture,
% 11.70/1.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_41,plain,
% 11.70/1.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2058,plain,
% 11.70/1.99      ( v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 11.70/1.99      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,X1_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_1847,c_33,c_34,c_35,c_40,c_41]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2059,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 11.70/1.99      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,X1_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top ),
% 11.70/1.99      inference(renaming,[status(thm)],[c_2058]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2065,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 11.70/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_903,c_2059]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.70/1.99      | ~ m1_pre_topc(X3,X1)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.70/1.99      | v2_struct_0(X1)
% 11.70/1.99      | v2_struct_0(X2)
% 11.70/1.99      | ~ v2_pre_topc(X2)
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | ~ l1_pre_topc(X2)
% 11.70/1.99      | ~ l1_pre_topc(X1)
% 11.70/1.99      | ~ v1_funct_1(X0)
% 11.70/1.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 11.70/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_389,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X0_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X0_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X0_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51)
% 11.70/1.99      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_886,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
% 11.70/1.99      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X0_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X0_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X0_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1561,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 11.70/1.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_900,c_886]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_29,negated_conjecture,
% 11.70/1.99      ( ~ v2_struct_0(sK0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_30,plain,
% 11.70/1.99      ( v2_struct_0(sK0) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_28,negated_conjecture,
% 11.70/1.99      ( v2_pre_topc(sK0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_31,plain,
% 11.70/1.99      ( v2_pre_topc(sK0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_27,negated_conjecture,
% 11.70/1.99      ( l1_pre_topc(sK0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_32,plain,
% 11.70/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1739,plain,
% 11.70/1.99      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_1561,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1740,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top ),
% 11.70/1.99      inference(renaming,[status(thm)],[c_1739]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1745,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_903,c_1740]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2069,plain,
% 11.70/1.99      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 11.70/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.70/1.99      inference(light_normalisation,[status(thm)],[c_2065,c_1745]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_39,plain,
% 11.70/1.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_7,plain,
% 11.70/1.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_55,plain,
% 11.70/1.99      ( m1_pre_topc(X0,X0) = iProver_top
% 11.70/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_57,plain,
% 11.70/1.99      ( m1_pre_topc(sK0,sK0) = iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_55]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2221,plain,
% 11.70/1.99      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_2069,c_30,c_31,c_32,c_39,c_57]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_22,negated_conjecture,
% 11.70/1.99      ( m1_pre_topc(sK2,sK0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_369,negated_conjecture,
% 11.70/1.99      ( m1_pre_topc(sK2,sK0) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_22]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_905,plain,
% 11.70/1.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2066,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_905,c_2059]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1746,plain,
% 11.70/1.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_905,c_1740]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2068,plain,
% 11.70/1.99      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.70/1.99      inference(light_normalisation,[status(thm)],[c_2066,c_1746]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_37,plain,
% 11.70/1.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2127,plain,
% 11.70/1.99      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_2068,c_30,c_31,c_32,c_37,c_57]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_8,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
% 11.70/1.99      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
% 11.70/1.99      | ~ m1_pre_topc(X3,X2)
% 11.70/1.99      | ~ m1_pre_topc(X3,X4)
% 11.70/1.99      | ~ m1_pre_topc(X4,X2)
% 11.70/1.99      | ~ m1_pre_topc(X0,X3)
% 11.70/1.99      | ~ m1_pre_topc(X0,X2)
% 11.70/1.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
% 11.70/1.99      | v2_struct_0(X2)
% 11.70/1.99      | v2_struct_0(X1)
% 11.70/1.99      | v2_struct_0(X3)
% 11.70/1.99      | v2_struct_0(X0)
% 11.70/1.99      | v2_struct_0(X4)
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | ~ v2_pre_topc(X2)
% 11.70/1.99      | ~ l1_pre_topc(X1)
% 11.70/1.99      | ~ l1_pre_topc(X2)
% 11.70/1.99      | ~ v1_funct_1(X5) ),
% 11.70/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_383,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k3_tmap_1(X2_50,X1_50,X4_50,X3_50,X0_51)),k3_tmap_1(X2_50,X1_50,X4_50,X0_50,X0_51))
% 11.70/1.99      | ~ v1_funct_2(X0_51,u1_struct_0(X4_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X3_50)
% 11.70/1.99      | ~ m1_pre_topc(X3_50,X2_50)
% 11.70/1.99      | ~ m1_pre_topc(X3_50,X4_50)
% 11.70/1.99      | ~ m1_pre_topc(X4_50,X2_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X2_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X4_50)
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(X3_50)
% 11.70/1.99      | v2_struct_0(X2_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X2_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X2_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_892,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k3_tmap_1(X2_50,X1_50,X4_50,X3_50,X0_51)),k3_tmap_1(X2_50,X1_50,X4_50,X0_50,X0_51)) = iProver_top
% 11.70/1.99      | v1_funct_2(X0_51,u1_struct_0(X4_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X3_50,X4_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X4_50,X2_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X4_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X0_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X2_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X3_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2131,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 11.70/1.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X0_50) = iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_struct_0(sK2) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2127,c_892]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_23,negated_conjecture,
% 11.70/1.99      ( ~ v2_struct_0(sK2) ),
% 11.70/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_36,plain,
% 11.70/1.99      ( v2_struct_0(sK2) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_42,plain,
% 11.70/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3526,plain,
% 11.70/1.99      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X0_50) = iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_2131,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_40,
% 11.70/1.99                 c_41,c_42,c_57]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3527,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X0_50,sK2,k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,X0_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X0_50) = iProver_top ),
% 11.70/1.99      inference(renaming,[status(thm)],[c_3526]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3533,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 11.70/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 11.70/1.99      | v2_struct_0(sK3) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2221,c_3527]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_21,negated_conjecture,
% 11.70/1.99      ( ~ v2_struct_0(sK3) ),
% 11.70/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_38,plain,
% 11.70/1.99      ( v2_struct_0(sK3) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_16,negated_conjecture,
% 11.70/1.99      ( m1_pre_topc(sK2,sK3) ),
% 11.70/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_43,plain,
% 11.70/1.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3538,plain,
% 11.70/1.99      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_3533,c_38,c_39,c_43]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.70/1.99      | ~ m1_pre_topc(X3,X4)
% 11.70/1.99      | ~ m1_pre_topc(X1,X4)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.70/1.99      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 11.70/1.99      | v2_struct_0(X4)
% 11.70/1.99      | v2_struct_0(X2)
% 11.70/1.99      | ~ v2_pre_topc(X2)
% 11.70/1.99      | ~ v2_pre_topc(X4)
% 11.70/1.99      | ~ l1_pre_topc(X2)
% 11.70/1.99      | ~ l1_pre_topc(X4)
% 11.70/1.99      | ~ v1_funct_1(X0) ),
% 11.70/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_387,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X3_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X3_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.70/1.99      | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X3_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X3_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X3_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_4]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_888,plain,
% 11.70/1.99      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) = iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X2_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1,plain,
% 11.70/1.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 11.70/1.99      | ~ v1_funct_2(X3,X0,X1)
% 11.70/1.99      | ~ v1_funct_2(X2,X0,X1)
% 11.70/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.70/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.70/1.99      | ~ v1_funct_1(X3)
% 11.70/1.99      | ~ v1_funct_1(X2)
% 11.70/1.99      | X2 = X3 ),
% 11.70/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_390,plain,
% 11.70/1.99      ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
% 11.70/1.99      | ~ v1_funct_2(X1_51,X0_52,X1_52)
% 11.70/1.99      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 11.70/1.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 11.70/1.99      | ~ v1_funct_1(X0_51)
% 11.70/1.99      | ~ v1_funct_1(X1_51)
% 11.70/1.99      | X0_51 = X1_51 ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_885,plain,
% 11.70/1.99      ( X0_51 = X1_51
% 11.70/1.99      | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
% 11.70/1.99      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 11.70/1.99      | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 11.70/1.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top
% 11.70/1.99      | v1_funct_1(X1_51) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1935,plain,
% 11.70/1.99      ( k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51) = X1_51
% 11.70/1.99      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),X1_51) != iProver_top
% 11.70/1.99      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | v1_funct_2(X1_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | v1_funct_2(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X0_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X0_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X0_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top
% 11.70/1.99      | v1_funct_1(X1_51) != iProver_top
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51)) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_888,c_885]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4441,plain,
% 11.70/1.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 11.70/1.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 11.70/1.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 11.70/1.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_3538,c_1935]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_4469,plain,
% 11.70/1.99      ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.70/1.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
% 11.70/1.99      | k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_4441]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_6,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.70/1.99      | ~ m1_pre_topc(X3,X4)
% 11.70/1.99      | ~ m1_pre_topc(X1,X4)
% 11.70/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.70/1.99      | v2_struct_0(X4)
% 11.70/1.99      | v2_struct_0(X2)
% 11.70/1.99      | ~ v2_pre_topc(X2)
% 11.70/1.99      | ~ v2_pre_topc(X4)
% 11.70/1.99      | ~ l1_pre_topc(X2)
% 11.70/1.99      | ~ l1_pre_topc(X4)
% 11.70/1.99      | ~ v1_funct_1(X0)
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_385,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X3_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X3_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X3_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X3_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X3_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51)
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_6]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_989,plain,
% 11.70/1.99      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(X1_50,X2_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X2_50)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X2_50)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(X2_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X2_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(X0_51)
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_385]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3444,plain,
% 11.70/1.99      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,X0_50)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(X0_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X0_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_989]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_3446,plain,
% 11.70/1.99      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_3444]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_401,plain,
% 11.70/1.99      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
% 11.70/1.99      | r1_tmap_1(X0_50,X1_50,X2_51,X3_51)
% 11.70/1.99      | X2_51 != X0_51
% 11.70/1.99      | X3_51 != X1_51 ),
% 11.70/1.99      theory(equality) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1110,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK2,sK1,X0_51,X1_51)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != X0_51
% 11.70/1.99      | sK6 != X1_51 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_401]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1158,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK2,sK1,X0_51,sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != X0_51
% 11.70/1.99      | sK6 != sK6 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1110]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1381,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51),sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51)
% 11.70/1.99      | sK6 != sK6 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1158]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2590,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 11.70/1.99      | sK6 != sK6 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1381]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2592,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
% 11.70/1.99      | k2_tmap_1(sK0,sK1,sK4,sK2) != k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 11.70/1.99      | sK6 != sK6 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_2590]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_890,plain,
% 11.70/1.99      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X2_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1566,plain,
% 11.70/1.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,X1_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_900,c_890]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2051,plain,
% 11.70/1.99      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,X1_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top ),
% 11.70/1.99      inference(global_propositional_subsumption,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_1566,c_33,c_34,c_35,c_40,c_41]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2052,plain,
% 11.70/1.99      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,X1_50) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
% 11.70/1.99      inference(renaming,[status(thm)],[c_2051]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2228,plain,
% 11.70/1.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2221,c_2052]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2240,plain,
% 11.70/1.99      ( ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK0,sK0)
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2228]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_889,plain,
% 11.70/1.99      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 11.70/1.99      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 11.70/1.99      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 11.70/1.99      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 11.70/1.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 11.70/1.99      | v2_struct_0(X1_50) = iProver_top
% 11.70/1.99      | v2_struct_0(X2_50) = iProver_top
% 11.70/1.99      | v2_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | v2_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X1_50) != iProver_top
% 11.70/1.99      | l1_pre_topc(X2_50) != iProver_top
% 11.70/1.99      | v1_funct_1(X0_51) != iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2227,plain,
% 11.70/1.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 11.70/1.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2221,c_889]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2239,plain,
% 11.70/1.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK0,sK0)
% 11.70/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(sK4) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2227]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2226,plain,
% 11.70/1.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 11.70/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2221,c_888]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2238,plain,
% 11.70/1.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK0,sK0)
% 11.70/1.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(sK4) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2226]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2134,plain,
% 11.70/1.99      ( m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2127,c_2052]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2146,plain,
% 11.70/1.99      ( ~ m1_pre_topc(sK0,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2134]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2133,plain,
% 11.70/1.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 11.70/1.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2127,c_889]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2145,plain,
% 11.70/1.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.70/1.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK0,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(sK4) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2133]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2132,plain,
% 11.70/1.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 11.70/1.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 11.70/1.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 11.70/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.70/1.99      | v2_struct_0(sK0) = iProver_top
% 11.70/1.99      | v2_struct_0(sK1) = iProver_top
% 11.70/1.99      | v2_pre_topc(sK0) != iProver_top
% 11.70/1.99      | v2_pre_topc(sK1) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK0) != iProver_top
% 11.70/1.99      | l1_pre_topc(sK1) != iProver_top
% 11.70/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.70/1.99      inference(superposition,[status(thm)],[c_2127,c_888]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_2144,plain,
% 11.70/1.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK0,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.70/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(sK4) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2132]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_10,plain,
% 11.70/1.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 11.70/1.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 11.70/1.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 11.70/1.99      | ~ m1_pre_topc(X4,X5)
% 11.70/1.99      | ~ m1_pre_topc(X4,X0)
% 11.70/1.99      | ~ m1_pre_topc(X0,X5)
% 11.70/1.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 11.70/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.70/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.70/1.99      | v2_struct_0(X5)
% 11.70/1.99      | v2_struct_0(X1)
% 11.70/1.99      | v2_struct_0(X4)
% 11.70/1.99      | v2_struct_0(X0)
% 11.70/1.99      | ~ v2_pre_topc(X1)
% 11.70/1.99      | ~ v2_pre_topc(X5)
% 11.70/1.99      | ~ l1_pre_topc(X1)
% 11.70/1.99      | ~ l1_pre_topc(X5)
% 11.70/1.99      | ~ v1_funct_1(X2) ),
% 11.70/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_381,plain,
% 11.70/1.99      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
% 11.70/1.99      | r1_tmap_1(X2_50,X1_50,k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51)
% 11.70/1.99      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X3_50)
% 11.70/1.99      | ~ m1_pre_topc(X2_50,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X3_50)
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(X3_50)
% 11.70/1.99      | v2_struct_0(X2_50)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(X3_50)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(X3_50)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_10]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_984,plain,
% 11.70/1.99      ( ~ r1_tmap_1(X0_50,sK1,X0_51,X1_51)
% 11.70/1.99      | r1_tmap_1(X1_50,sK1,k3_tmap_1(X2_50,sK1,X0_50,X1_50,X0_51),X1_51)
% 11.70/1.99      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(X1_50,X2_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X2_50)
% 11.70/1.99      | ~ m1_pre_topc(X1_50,X0_50)
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(X1_50))
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(X2_50)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(X2_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X2_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_381]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1229,plain,
% 11.70/1.99      ( r1_tmap_1(X0_50,sK1,k3_tmap_1(X1_50,sK1,sK3,X0_50,X0_51),X1_51)
% 11.70/1.99      | ~ r1_tmap_1(sK3,sK1,X0_51,X1_51)
% 11.70/1.99      | ~ v1_funct_2(X0_51,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(X0_50,X1_50)
% 11.70/1.99      | ~ m1_pre_topc(X0_50,sK3)
% 11.70/1.99      | ~ m1_pre_topc(sK3,X1_50)
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK3))
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X1_50)
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(sK3)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | ~ v2_pre_topc(X1_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X1_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_984]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1330,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK3,sK1,X0_51,X1_51)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51),X1_51)
% 11.70/1.99      | ~ v1_funct_2(X0_51,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK3)
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK3))
% 11.70/1.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(sK3)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | v2_struct_0(sK2)
% 11.70/1.99      | ~ v2_pre_topc(X0_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X0_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1229]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1380,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK3,sK1,X0_51,sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,X0_51),sK6)
% 11.70/1.99      | ~ v1_funct_2(X0_51,u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK3)
% 11.70/1.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 11.70/1.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(sK3)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | v2_struct_0(sK2)
% 11.70/1.99      | ~ v2_pre_topc(X0_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X0_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(X0_51) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1330]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1750,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
% 11.70/1.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,X0_50)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK3)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 11.70/1.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 11.70/1.99      | v2_struct_0(X0_50)
% 11.70/1.99      | v2_struct_0(sK3)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | v2_struct_0(sK2)
% 11.70/1.99      | ~ v2_pre_topc(X0_50)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(X0_50)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1380]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1752,plain,
% 11.70/1.99      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6)
% 11.70/1.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK6)
% 11.70/1.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 11.70/1.99      | ~ m1_pre_topc(sK3,sK0)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK3)
% 11.70/1.99      | ~ m1_pre_topc(sK2,sK0)
% 11.70/1.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 11.70/1.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 11.70/1.99      | ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 11.70/1.99      | v2_struct_0(sK3)
% 11.70/1.99      | v2_struct_0(sK0)
% 11.70/1.99      | v2_struct_0(sK1)
% 11.70/1.99      | v2_struct_0(sK2)
% 11.70/1.99      | ~ v2_pre_topc(sK0)
% 11.70/1.99      | ~ v2_pre_topc(sK1)
% 11.70/1.99      | ~ l1_pre_topc(sK0)
% 11.70/1.99      | ~ l1_pre_topc(sK1)
% 11.70/1.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_1750]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_393,plain,( X0_51 = X0_51 ),theory(equality) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1698,plain,
% 11.70/1.99      ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_393]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_1348,plain,
% 11.70/1.99      ( sK6 = sK6 ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_393]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_12,negated_conjecture,
% 11.70/1.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 11.70/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_379,negated_conjecture,
% 11.70/1.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_12]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_896,plain,
% 11.70/1.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_13,negated_conjecture,
% 11.70/1.99      ( sK5 = sK6 ),
% 11.70/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_378,negated_conjecture,
% 11.70/1.99      ( sK5 = sK6 ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_13]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_914,plain,
% 11.70/1.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
% 11.70/1.99      inference(light_normalisation,[status(thm)],[c_896,c_378]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_933,plain,
% 11.70/1.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_914]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_15,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_376,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 11.70/1.99      inference(subtyping,[status(esa)],[c_15]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_898,plain,
% 11.70/1.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 11.70/1.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_913,plain,
% 11.70/1.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 11.70/1.99      inference(light_normalisation,[status(thm)],[c_898,c_378]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_918,plain,
% 11.70/1.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 11.70/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_913]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_56,plain,
% 11.70/1.99      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 11.70/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_11,negated_conjecture,
% 11.70/1.99      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
% 11.70/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(c_14,negated_conjecture,
% 11.70/1.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 11.70/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.70/1.99  
% 11.70/1.99  cnf(contradiction,plain,
% 11.70/1.99      ( $false ),
% 11.70/1.99      inference(minisat,
% 11.70/1.99                [status(thm)],
% 11.70/1.99                [c_31758,c_6530,c_4469,c_3446,c_2592,c_2240,c_2239,
% 11.70/1.99                 c_2238,c_2146,c_2145,c_2144,c_1752,c_1698,c_1348,c_933,
% 11.70/1.99                 c_918,c_56,c_11,c_14,c_16,c_17,c_18,c_19,c_20,c_21,c_22,
% 11.70/1.99                 c_23,c_24,c_25,c_26,c_27,c_28,c_29]) ).
% 11.70/1.99  
% 11.70/1.99  
% 11.70/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.70/1.99  
% 11.70/1.99  ------                               Statistics
% 11.70/1.99  
% 11.70/1.99  ------ General
% 11.70/1.99  
% 11.70/1.99  abstr_ref_over_cycles:                  0
% 11.70/1.99  abstr_ref_under_cycles:                 0
% 11.70/1.99  gc_basic_clause_elim:                   0
% 11.70/1.99  forced_gc_time:                         0
% 11.70/1.99  parsing_time:                           0.013
% 11.70/1.99  unif_index_cands_time:                  0.
% 11.70/1.99  unif_index_add_time:                    0.
% 11.70/1.99  orderings_time:                         0.
% 11.70/1.99  out_proof_time:                         0.016
% 11.70/1.99  total_time:                             1.166
% 11.70/1.99  num_of_symbols:                         54
% 11.70/1.99  num_of_terms:                           16019
% 11.70/1.99  
% 11.70/1.99  ------ Preprocessing
% 11.70/1.99  
% 11.70/1.99  num_of_splits:                          0
% 11.70/1.99  num_of_split_atoms:                     0
% 11.70/1.99  num_of_reused_defs:                     0
% 11.70/1.99  num_eq_ax_congr_red:                    32
% 11.70/1.99  num_of_sem_filtered_clauses:            1
% 11.70/1.99  num_of_subtypes:                        4
% 11.70/1.99  monotx_restored_types:                  0
% 11.70/1.99  sat_num_of_epr_types:                   0
% 11.70/1.99  sat_num_of_non_cyclic_types:            0
% 11.70/1.99  sat_guarded_non_collapsed_types:        1
% 11.70/1.99  num_pure_diseq_elim:                    0
% 11.70/1.99  simp_replaced_by:                       0
% 11.70/1.99  res_preprocessed:                       109
% 11.70/1.99  prep_upred:                             0
% 11.70/1.99  prep_unflattend:                        8
% 11.70/1.99  smt_new_axioms:                         0
% 11.70/1.99  pred_elim_cands:                        9
% 11.70/1.99  pred_elim:                              0
% 11.70/1.99  pred_elim_cl:                           0
% 11.70/1.99  pred_elim_cycles:                       1
% 11.70/1.99  merged_defs:                            0
% 11.70/1.99  merged_defs_ncl:                        0
% 11.70/1.99  bin_hyper_res:                          0
% 11.70/1.99  prep_cycles:                            3
% 11.70/1.99  pred_elim_time:                         0.004
% 11.70/1.99  splitting_time:                         0.
% 11.70/1.99  sem_filter_time:                        0.
% 11.70/1.99  monotx_time:                            0.
% 11.70/1.99  subtype_inf_time:                       0.
% 11.70/1.99  
% 11.70/1.99  ------ Problem properties
% 11.70/1.99  
% 11.70/1.99  clauses:                                30
% 11.70/1.99  conjectures:                            19
% 11.70/1.99  epr:                                    15
% 11.70/1.99  horn:                                   23
% 11.70/1.99  ground:                                 19
% 11.70/1.99  unary:                                  19
% 11.70/1.99  binary:                                 1
% 11.70/1.99  lits:                                   134
% 11.70/1.99  lits_eq:                                4
% 11.70/1.99  fd_pure:                                0
% 11.70/1.99  fd_pseudo:                              0
% 11.70/1.99  fd_cond:                                0
% 11.70/1.99  fd_pseudo_cond:                         1
% 11.70/1.99  ac_symbols:                             0
% 11.70/1.99  
% 11.70/1.99  ------ Propositional Solver
% 11.70/1.99  
% 11.70/1.99  prop_solver_calls:                      36
% 11.70/1.99  prop_fast_solver_calls:                 5456
% 11.70/1.99  smt_solver_calls:                       0
% 11.70/1.99  smt_fast_solver_calls:                  0
% 11.70/1.99  prop_num_of_clauses:                    8137
% 11.70/1.99  prop_preprocess_simplified:             20696
% 11.70/1.99  prop_fo_subsumed:                       1711
% 11.70/1.99  prop_solver_time:                       0.
% 11.70/1.99  smt_solver_time:                        0.
% 11.70/1.99  smt_fast_solver_time:                   0.
% 11.70/1.99  prop_fast_solver_time:                  0.
% 11.70/1.99  prop_unsat_core_time:                   0.001
% 11.70/1.99  
% 11.70/1.99  ------ QBF
% 11.70/1.99  
% 11.70/1.99  qbf_q_res:                              0
% 11.70/1.99  qbf_num_tautologies:                    0
% 11.70/1.99  qbf_prep_cycles:                        0
% 11.70/1.99  
% 11.70/1.99  ------ BMC1
% 11.70/1.99  
% 11.70/1.99  bmc1_current_bound:                     -1
% 11.70/1.99  bmc1_last_solved_bound:                 -1
% 11.70/1.99  bmc1_unsat_core_size:                   -1
% 11.70/1.99  bmc1_unsat_core_parents_size:           -1
% 11.70/1.99  bmc1_merge_next_fun:                    0
% 11.70/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.70/1.99  
% 11.70/1.99  ------ Instantiation
% 11.70/1.99  
% 11.70/1.99  inst_num_of_clauses:                    3143
% 11.70/1.99  inst_num_in_passive:                    959
% 11.70/1.99  inst_num_in_active:                     1809
% 11.70/1.99  inst_num_in_unprocessed:                374
% 11.70/1.99  inst_num_of_loops:                      1897
% 11.70/1.99  inst_num_of_learning_restarts:          0
% 11.70/1.99  inst_num_moves_active_passive:          73
% 11.70/1.99  inst_lit_activity:                      0
% 11.70/1.99  inst_lit_activity_moves:                0
% 11.70/1.99  inst_num_tautologies:                   0
% 11.70/1.99  inst_num_prop_implied:                  0
% 11.70/1.99  inst_num_existing_simplified:           0
% 11.70/1.99  inst_num_eq_res_simplified:             0
% 11.70/1.99  inst_num_child_elim:                    0
% 11.70/1.99  inst_num_of_dismatching_blockings:      3144
% 11.70/1.99  inst_num_of_non_proper_insts:           6830
% 11.70/2.00  inst_num_of_duplicates:                 0
% 11.70/2.00  inst_inst_num_from_inst_to_res:         0
% 11.70/2.00  inst_dismatching_checking_time:         0.
% 11.70/2.00  
% 11.70/2.00  ------ Resolution
% 11.70/2.00  
% 11.70/2.00  res_num_of_clauses:                     0
% 11.70/2.00  res_num_in_passive:                     0
% 11.70/2.00  res_num_in_active:                      0
% 11.70/2.00  res_num_of_loops:                       112
% 11.70/2.00  res_forward_subset_subsumed:            352
% 11.70/2.00  res_backward_subset_subsumed:           0
% 11.70/2.00  res_forward_subsumed:                   0
% 11.70/2.00  res_backward_subsumed:                  0
% 11.70/2.00  res_forward_subsumption_resolution:     2
% 11.70/2.00  res_backward_subsumption_resolution:    0
% 11.70/2.00  res_clause_to_clause_subsumption:       1245
% 11.70/2.00  res_orphan_elimination:                 0
% 11.70/2.00  res_tautology_del:                      1031
% 11.70/2.00  res_num_eq_res_simplified:              0
% 11.70/2.00  res_num_sel_changes:                    0
% 11.70/2.00  res_moves_from_active_to_pass:          0
% 11.70/2.00  
% 11.70/2.00  ------ Superposition
% 11.70/2.00  
% 11.70/2.00  sup_time_total:                         0.
% 11.70/2.00  sup_time_generating:                    0.
% 11.70/2.00  sup_time_sim_full:                      0.
% 11.70/2.00  sup_time_sim_immed:                     0.
% 11.70/2.00  
% 11.70/2.00  sup_num_of_clauses:                     443
% 11.70/2.00  sup_num_in_active:                      307
% 11.70/2.00  sup_num_in_passive:                     136
% 11.70/2.00  sup_num_of_loops:                       378
% 11.70/2.00  sup_fw_superposition:                   346
% 11.70/2.00  sup_bw_superposition:                   262
% 11.70/2.00  sup_immediate_simplified:               143
% 11.70/2.00  sup_given_eliminated:                   4
% 11.70/2.00  comparisons_done:                       0
% 11.70/2.00  comparisons_avoided:                    0
% 11.70/2.00  
% 11.70/2.00  ------ Simplifications
% 11.70/2.00  
% 11.70/2.00  
% 11.70/2.00  sim_fw_subset_subsumed:                 24
% 11.70/2.00  sim_bw_subset_subsumed:                 15
% 11.70/2.00  sim_fw_subsumed:                        32
% 11.70/2.00  sim_bw_subsumed:                        10
% 11.70/2.00  sim_fw_subsumption_res:                 0
% 11.70/2.00  sim_bw_subsumption_res:                 0
% 11.70/2.00  sim_tautology_del:                      1
% 11.70/2.00  sim_eq_tautology_del:                   19
% 11.70/2.00  sim_eq_res_simp:                        0
% 11.70/2.00  sim_fw_demodulated:                     24
% 11.70/2.00  sim_bw_demodulated:                     58
% 11.70/2.00  sim_light_normalised:                   138
% 11.70/2.00  sim_joinable_taut:                      0
% 11.70/2.00  sim_joinable_simp:                      0
% 11.70/2.00  sim_ac_normalised:                      0
% 11.70/2.00  sim_smt_subsumption:                    0
% 11.70/2.00  
%------------------------------------------------------------------------------
