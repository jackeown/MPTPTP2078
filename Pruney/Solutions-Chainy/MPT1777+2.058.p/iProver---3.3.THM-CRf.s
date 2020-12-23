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

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  218 (1636 expanded)
%              Number of clauses        :  130 ( 401 expanded)
%              Number of leaves         :   25 ( 689 expanded)
%              Depth                    :   19
%              Number of atoms          :  957 (20642 expanded)
%              Number of equality atoms :  325 (3159 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f80,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f63,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(ennf_transformation,[],[f16])).

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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
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

fof(f90,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(equality_resolution,[],[f70])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f52])).

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

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_948,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_982,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_948,c_0])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_925,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_943,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2305,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_925,c_943])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1647,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

cnf(c_1648,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_3890,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2305,c_39,c_1648])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_944,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3895,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3890,c_944])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_945,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4034,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3895,c_945])).

cnf(c_11,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_939,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4049,plain,
    ( m1_connsp_2(X0,sK3,X1) = iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_939])).

cnf(c_4072,plain,
    ( m1_connsp_2(X0,sK3,X1) = iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4049,c_4034])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_946,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2898,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_925,c_946])).

cnf(c_19189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | m1_connsp_2(X0,sK3,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4072,c_38,c_39,c_45,c_1648,c_2898])).

cnf(c_19190,plain,
    ( m1_connsp_2(X0,sK3,X1) = iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_19189])).

cnf(c_19200,plain,
    ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
    | v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_19190])).

cnf(c_2945,plain,
    ( m1_connsp_2(u1_struct_0(X0),X0,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_939])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_73,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_84,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_87,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_309,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1351,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | X0 != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1524,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0)
    | ~ v3_pre_topc(k2_struct_0(X0),X0)
    | u1_struct_0(X0) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_1525,plain,
    ( u1_struct_0(X0) != k2_struct_0(X0)
    | v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | v3_pre_topc(k2_struct_0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_9444,plain,
    ( m1_connsp_2(u1_struct_0(X0),X0,X1) = iProver_top
    | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2945,c_73,c_84,c_87,c_1525])).

cnf(c_9457,plain,
    ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_9444])).

cnf(c_9492,plain,
    ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9457,c_4034])).

cnf(c_19447,plain,
    ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
    | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19200,c_38,c_39,c_45,c_1648,c_2898,c_9492])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_931,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1003,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_931,c_20])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
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
    inference(cnf_transformation,[],[f90])).

cnf(c_934,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_connsp_2(X6,X0,X3) != iProver_top
    | r1_tarski(X6,u1_struct_0(X4)) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_935,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1153,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_connsp_2(X6,X0,X3) != iProver_top
    | r1_tarski(X6,u1_struct_0(X4)) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_934,c_935])).

cnf(c_3918,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_connsp_2(X0,sK3,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_1153])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_921,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1895,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_944])).

cnf(c_3313,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1895,c_945])).

cnf(c_3919,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_connsp_2(X0,sK3,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3918,c_3313])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_47,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_53,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_930,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_977,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_930,c_20])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1649,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

cnf(c_1650,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_937,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_262,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_6])).

cnf(c_263,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_915,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_1286,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_915])).

cnf(c_2587,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1286,c_39,c_1650])).

cnf(c_2588,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_2587])).

cnf(c_2595,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_2588])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_928,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3407,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3313,c_928])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_927,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3408,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3313,c_927])).

cnf(c_16715,plain,
    ( m1_connsp_2(X0,sK3,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3919,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,c_47,c_50,c_53,c_977,c_1650,c_2595,c_3407,c_3408])).

cnf(c_923,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2306,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_943])).

cnf(c_4260,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_39,c_1650])).

cnf(c_4265,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4260,c_944])).

cnf(c_4593,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_4265,c_945])).

cnf(c_16721,plain,
    ( m1_connsp_2(X0,sK3,sK5) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16715,c_4034,c_4593])).

cnf(c_16728,plain,
    ( m1_connsp_2(k2_struct_0(sK3),sK3,sK5) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_16721])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_938,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2728,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK3,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_938])).

cnf(c_2775,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_2728])).

cnf(c_14,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_936,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4046,plain,
    ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_936])).

cnf(c_7770,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4593,c_4046])).

cnf(c_16870,plain,
    ( m1_connsp_2(k2_struct_0(sK3),sK3,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16728,c_39,c_1650,c_2775,c_7770])).

cnf(c_19456,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19447,c_16870])).

cnf(c_929,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4037,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4034,c_929])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_947,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4257,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4037,c_947])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_942,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4047,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_942])).

cnf(c_1597,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1598,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19456,c_4257,c_4047,c_4037,c_1648,c_1598,c_45,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.11/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/1.00  
% 4.11/1.00  ------  iProver source info
% 4.11/1.00  
% 4.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/1.00  git: non_committed_changes: false
% 4.11/1.00  git: last_make_outside_of_git: false
% 4.11/1.00  
% 4.11/1.00  ------ 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options
% 4.11/1.00  
% 4.11/1.00  --out_options                           all
% 4.11/1.00  --tptp_safe_out                         true
% 4.11/1.00  --problem_path                          ""
% 4.11/1.00  --include_path                          ""
% 4.11/1.00  --clausifier                            res/vclausify_rel
% 4.11/1.00  --clausifier_options                    --mode clausify
% 4.11/1.00  --stdin                                 false
% 4.11/1.00  --stats_out                             sel
% 4.11/1.00  
% 4.11/1.00  ------ General Options
% 4.11/1.00  
% 4.11/1.00  --fof                                   false
% 4.11/1.00  --time_out_real                         604.99
% 4.11/1.00  --time_out_virtual                      -1.
% 4.11/1.00  --symbol_type_check                     false
% 4.11/1.00  --clausify_out                          false
% 4.11/1.00  --sig_cnt_out                           false
% 4.11/1.00  --trig_cnt_out                          false
% 4.11/1.00  --trig_cnt_out_tolerance                1.
% 4.11/1.00  --trig_cnt_out_sk_spl                   false
% 4.11/1.00  --abstr_cl_out                          false
% 4.11/1.00  
% 4.11/1.00  ------ Global Options
% 4.11/1.00  
% 4.11/1.00  --schedule                              none
% 4.11/1.00  --add_important_lit                     false
% 4.11/1.00  --prop_solver_per_cl                    1000
% 4.11/1.00  --min_unsat_core                        false
% 4.11/1.00  --soft_assumptions                      false
% 4.11/1.00  --soft_lemma_size                       3
% 4.11/1.00  --prop_impl_unit_size                   0
% 4.11/1.00  --prop_impl_unit                        []
% 4.11/1.00  --share_sel_clauses                     true
% 4.11/1.00  --reset_solvers                         false
% 4.11/1.00  --bc_imp_inh                            [conj_cone]
% 4.11/1.00  --conj_cone_tolerance                   3.
% 4.11/1.00  --extra_neg_conj                        none
% 4.11/1.00  --large_theory_mode                     true
% 4.11/1.00  --prolific_symb_bound                   200
% 4.11/1.00  --lt_threshold                          2000
% 4.11/1.00  --clause_weak_htbl                      true
% 4.11/1.00  --gc_record_bc_elim                     false
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing Options
% 4.11/1.00  
% 4.11/1.00  --preprocessing_flag                    true
% 4.11/1.00  --time_out_prep_mult                    0.1
% 4.11/1.00  --splitting_mode                        input
% 4.11/1.00  --splitting_grd                         true
% 4.11/1.00  --splitting_cvd                         false
% 4.11/1.00  --splitting_cvd_svl                     false
% 4.11/1.00  --splitting_nvd                         32
% 4.11/1.00  --sub_typing                            true
% 4.11/1.00  --prep_gs_sim                           false
% 4.11/1.00  --prep_unflatten                        true
% 4.11/1.00  --prep_res_sim                          true
% 4.11/1.00  --prep_upred                            true
% 4.11/1.00  --prep_sem_filter                       exhaustive
% 4.11/1.00  --prep_sem_filter_out                   false
% 4.11/1.00  --pred_elim                             false
% 4.11/1.00  --res_sim_input                         true
% 4.11/1.00  --eq_ax_congr_red                       true
% 4.11/1.00  --pure_diseq_elim                       true
% 4.11/1.00  --brand_transform                       false
% 4.11/1.00  --non_eq_to_eq                          false
% 4.11/1.00  --prep_def_merge                        true
% 4.11/1.00  --prep_def_merge_prop_impl              false
% 4.11/1.00  --prep_def_merge_mbd                    true
% 4.11/1.00  --prep_def_merge_tr_red                 false
% 4.11/1.00  --prep_def_merge_tr_cl                  false
% 4.11/1.00  --smt_preprocessing                     true
% 4.11/1.00  --smt_ac_axioms                         fast
% 4.11/1.00  --preprocessed_out                      false
% 4.11/1.00  --preprocessed_stats                    false
% 4.11/1.00  
% 4.11/1.00  ------ Abstraction refinement Options
% 4.11/1.00  
% 4.11/1.00  --abstr_ref                             []
% 4.11/1.00  --abstr_ref_prep                        false
% 4.11/1.00  --abstr_ref_until_sat                   false
% 4.11/1.00  --abstr_ref_sig_restrict                funpre
% 4.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.00  --abstr_ref_under                       []
% 4.11/1.00  
% 4.11/1.00  ------ SAT Options
% 4.11/1.00  
% 4.11/1.00  --sat_mode                              false
% 4.11/1.00  --sat_fm_restart_options                ""
% 4.11/1.00  --sat_gr_def                            false
% 4.11/1.00  --sat_epr_types                         true
% 4.11/1.00  --sat_non_cyclic_types                  false
% 4.11/1.00  --sat_finite_models                     false
% 4.11/1.00  --sat_fm_lemmas                         false
% 4.11/1.00  --sat_fm_prep                           false
% 4.11/1.00  --sat_fm_uc_incr                        true
% 4.11/1.00  --sat_out_model                         small
% 4.11/1.00  --sat_out_clauses                       false
% 4.11/1.00  
% 4.11/1.00  ------ QBF Options
% 4.11/1.00  
% 4.11/1.00  --qbf_mode                              false
% 4.11/1.00  --qbf_elim_univ                         false
% 4.11/1.00  --qbf_dom_inst                          none
% 4.11/1.00  --qbf_dom_pre_inst                      false
% 4.11/1.00  --qbf_sk_in                             false
% 4.11/1.00  --qbf_pred_elim                         true
% 4.11/1.00  --qbf_split                             512
% 4.11/1.00  
% 4.11/1.00  ------ BMC1 Options
% 4.11/1.00  
% 4.11/1.00  --bmc1_incremental                      false
% 4.11/1.00  --bmc1_axioms                           reachable_all
% 4.11/1.00  --bmc1_min_bound                        0
% 4.11/1.00  --bmc1_max_bound                        -1
% 4.11/1.00  --bmc1_max_bound_default                -1
% 4.11/1.00  --bmc1_symbol_reachability              true
% 4.11/1.00  --bmc1_property_lemmas                  false
% 4.11/1.00  --bmc1_k_induction                      false
% 4.11/1.00  --bmc1_non_equiv_states                 false
% 4.11/1.00  --bmc1_deadlock                         false
% 4.11/1.00  --bmc1_ucm                              false
% 4.11/1.00  --bmc1_add_unsat_core                   none
% 4.11/1.00  --bmc1_unsat_core_children              false
% 4.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.00  --bmc1_out_stat                         full
% 4.11/1.00  --bmc1_ground_init                      false
% 4.11/1.00  --bmc1_pre_inst_next_state              false
% 4.11/1.00  --bmc1_pre_inst_state                   false
% 4.11/1.00  --bmc1_pre_inst_reach_state             false
% 4.11/1.00  --bmc1_out_unsat_core                   false
% 4.11/1.00  --bmc1_aig_witness_out                  false
% 4.11/1.00  --bmc1_verbose                          false
% 4.11/1.00  --bmc1_dump_clauses_tptp                false
% 4.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.00  --bmc1_dump_file                        -
% 4.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.00  --bmc1_ucm_extend_mode                  1
% 4.11/1.00  --bmc1_ucm_init_mode                    2
% 4.11/1.00  --bmc1_ucm_cone_mode                    none
% 4.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.00  --bmc1_ucm_relax_model                  4
% 4.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.00  --bmc1_ucm_layered_model                none
% 4.11/1.00  --bmc1_ucm_max_lemma_size               10
% 4.11/1.00  
% 4.11/1.00  ------ AIG Options
% 4.11/1.00  
% 4.11/1.00  --aig_mode                              false
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation Options
% 4.11/1.00  
% 4.11/1.00  --instantiation_flag                    true
% 4.11/1.00  --inst_sos_flag                         false
% 4.11/1.00  --inst_sos_phase                        true
% 4.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel_side                     num_symb
% 4.11/1.00  --inst_solver_per_active                1400
% 4.11/1.00  --inst_solver_calls_frac                1.
% 4.11/1.00  --inst_passive_queue_type               priority_queues
% 4.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.00  --inst_passive_queues_freq              [25;2]
% 4.11/1.00  --inst_dismatching                      true
% 4.11/1.00  --inst_eager_unprocessed_to_passive     true
% 4.11/1.00  --inst_prop_sim_given                   true
% 4.11/1.00  --inst_prop_sim_new                     false
% 4.11/1.00  --inst_subs_new                         false
% 4.11/1.00  --inst_eq_res_simp                      false
% 4.11/1.00  --inst_subs_given                       false
% 4.11/1.00  --inst_orphan_elimination               true
% 4.11/1.00  --inst_learning_loop_flag               true
% 4.11/1.00  --inst_learning_start                   3000
% 4.11/1.00  --inst_learning_factor                  2
% 4.11/1.00  --inst_start_prop_sim_after_learn       3
% 4.11/1.00  --inst_sel_renew                        solver
% 4.11/1.00  --inst_lit_activity_flag                true
% 4.11/1.00  --inst_restr_to_given                   false
% 4.11/1.00  --inst_activity_threshold               500
% 4.11/1.00  --inst_out_proof                        true
% 4.11/1.00  
% 4.11/1.00  ------ Resolution Options
% 4.11/1.00  
% 4.11/1.00  --resolution_flag                       true
% 4.11/1.00  --res_lit_sel                           adaptive
% 4.11/1.00  --res_lit_sel_side                      none
% 4.11/1.00  --res_ordering                          kbo
% 4.11/1.00  --res_to_prop_solver                    active
% 4.11/1.00  --res_prop_simpl_new                    false
% 4.11/1.00  --res_prop_simpl_given                  true
% 4.11/1.00  --res_passive_queue_type                priority_queues
% 4.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.00  --res_passive_queues_freq               [15;5]
% 4.11/1.00  --res_forward_subs                      full
% 4.11/1.00  --res_backward_subs                     full
% 4.11/1.00  --res_forward_subs_resolution           true
% 4.11/1.00  --res_backward_subs_resolution          true
% 4.11/1.00  --res_orphan_elimination                true
% 4.11/1.00  --res_time_limit                        2.
% 4.11/1.00  --res_out_proof                         true
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Options
% 4.11/1.00  
% 4.11/1.00  --superposition_flag                    true
% 4.11/1.00  --sup_passive_queue_type                priority_queues
% 4.11/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.00  --sup_passive_queues_freq               [1;4]
% 4.11/1.00  --demod_completeness_check              fast
% 4.11/1.00  --demod_use_ground                      true
% 4.11/1.00  --sup_to_prop_solver                    passive
% 4.11/1.00  --sup_prop_simpl_new                    true
% 4.11/1.00  --sup_prop_simpl_given                  true
% 4.11/1.00  --sup_fun_splitting                     false
% 4.11/1.00  --sup_smt_interval                      50000
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Simplification Setup
% 4.11/1.00  
% 4.11/1.00  --sup_indices_passive                   []
% 4.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_full_bw                           [BwDemod]
% 4.11/1.00  --sup_immed_triv                        [TrivRules]
% 4.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_immed_bw_main                     []
% 4.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  
% 4.11/1.00  ------ Combination Options
% 4.11/1.00  
% 4.11/1.00  --comb_res_mult                         3
% 4.11/1.00  --comb_sup_mult                         2
% 4.11/1.00  --comb_inst_mult                        10
% 4.11/1.00  
% 4.11/1.00  ------ Debug Options
% 4.11/1.00  
% 4.11/1.00  --dbg_backtrace                         false
% 4.11/1.00  --dbg_dump_prop_clauses                 false
% 4.11/1.00  --dbg_dump_prop_clauses_file            -
% 4.11/1.00  --dbg_out_stat                          false
% 4.11/1.00  ------ Parsing...
% 4.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/1.00  ------ Proving...
% 4.11/1.00  ------ Problem Properties 
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  clauses                                 37
% 4.11/1.00  conjectures                             19
% 4.11/1.00  EPR                                     19
% 4.11/1.00  Horn                                    33
% 4.11/1.00  unary                                   21
% 4.11/1.00  binary                                  3
% 4.11/1.00  lits                                    111
% 4.11/1.00  lits eq                                 4
% 4.11/1.00  fd_pure                                 0
% 4.11/1.00  fd_pseudo                               0
% 4.11/1.00  fd_cond                                 0
% 4.11/1.00  fd_pseudo_cond                          0
% 4.11/1.00  AC symbols                              0
% 4.11/1.00  
% 4.11/1.00  ------ Input Options Time Limit: Unbounded
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  ------ 
% 4.11/1.00  Current options:
% 4.11/1.00  ------ 
% 4.11/1.00  
% 4.11/1.00  ------ Input Options
% 4.11/1.00  
% 4.11/1.00  --out_options                           all
% 4.11/1.00  --tptp_safe_out                         true
% 4.11/1.00  --problem_path                          ""
% 4.11/1.00  --include_path                          ""
% 4.11/1.00  --clausifier                            res/vclausify_rel
% 4.11/1.00  --clausifier_options                    --mode clausify
% 4.11/1.00  --stdin                                 false
% 4.11/1.00  --stats_out                             sel
% 4.11/1.00  
% 4.11/1.00  ------ General Options
% 4.11/1.00  
% 4.11/1.00  --fof                                   false
% 4.11/1.00  --time_out_real                         604.99
% 4.11/1.00  --time_out_virtual                      -1.
% 4.11/1.00  --symbol_type_check                     false
% 4.11/1.00  --clausify_out                          false
% 4.11/1.00  --sig_cnt_out                           false
% 4.11/1.00  --trig_cnt_out                          false
% 4.11/1.00  --trig_cnt_out_tolerance                1.
% 4.11/1.00  --trig_cnt_out_sk_spl                   false
% 4.11/1.00  --abstr_cl_out                          false
% 4.11/1.00  
% 4.11/1.00  ------ Global Options
% 4.11/1.00  
% 4.11/1.00  --schedule                              none
% 4.11/1.00  --add_important_lit                     false
% 4.11/1.00  --prop_solver_per_cl                    1000
% 4.11/1.00  --min_unsat_core                        false
% 4.11/1.00  --soft_assumptions                      false
% 4.11/1.00  --soft_lemma_size                       3
% 4.11/1.00  --prop_impl_unit_size                   0
% 4.11/1.00  --prop_impl_unit                        []
% 4.11/1.00  --share_sel_clauses                     true
% 4.11/1.00  --reset_solvers                         false
% 4.11/1.00  --bc_imp_inh                            [conj_cone]
% 4.11/1.00  --conj_cone_tolerance                   3.
% 4.11/1.00  --extra_neg_conj                        none
% 4.11/1.00  --large_theory_mode                     true
% 4.11/1.00  --prolific_symb_bound                   200
% 4.11/1.00  --lt_threshold                          2000
% 4.11/1.00  --clause_weak_htbl                      true
% 4.11/1.00  --gc_record_bc_elim                     false
% 4.11/1.00  
% 4.11/1.00  ------ Preprocessing Options
% 4.11/1.00  
% 4.11/1.00  --preprocessing_flag                    true
% 4.11/1.00  --time_out_prep_mult                    0.1
% 4.11/1.00  --splitting_mode                        input
% 4.11/1.00  --splitting_grd                         true
% 4.11/1.00  --splitting_cvd                         false
% 4.11/1.00  --splitting_cvd_svl                     false
% 4.11/1.00  --splitting_nvd                         32
% 4.11/1.00  --sub_typing                            true
% 4.11/1.00  --prep_gs_sim                           false
% 4.11/1.00  --prep_unflatten                        true
% 4.11/1.00  --prep_res_sim                          true
% 4.11/1.00  --prep_upred                            true
% 4.11/1.00  --prep_sem_filter                       exhaustive
% 4.11/1.00  --prep_sem_filter_out                   false
% 4.11/1.00  --pred_elim                             false
% 4.11/1.00  --res_sim_input                         true
% 4.11/1.00  --eq_ax_congr_red                       true
% 4.11/1.00  --pure_diseq_elim                       true
% 4.11/1.00  --brand_transform                       false
% 4.11/1.00  --non_eq_to_eq                          false
% 4.11/1.00  --prep_def_merge                        true
% 4.11/1.00  --prep_def_merge_prop_impl              false
% 4.11/1.00  --prep_def_merge_mbd                    true
% 4.11/1.00  --prep_def_merge_tr_red                 false
% 4.11/1.00  --prep_def_merge_tr_cl                  false
% 4.11/1.00  --smt_preprocessing                     true
% 4.11/1.00  --smt_ac_axioms                         fast
% 4.11/1.00  --preprocessed_out                      false
% 4.11/1.00  --preprocessed_stats                    false
% 4.11/1.00  
% 4.11/1.00  ------ Abstraction refinement Options
% 4.11/1.00  
% 4.11/1.00  --abstr_ref                             []
% 4.11/1.00  --abstr_ref_prep                        false
% 4.11/1.00  --abstr_ref_until_sat                   false
% 4.11/1.00  --abstr_ref_sig_restrict                funpre
% 4.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/1.00  --abstr_ref_under                       []
% 4.11/1.00  
% 4.11/1.00  ------ SAT Options
% 4.11/1.00  
% 4.11/1.00  --sat_mode                              false
% 4.11/1.00  --sat_fm_restart_options                ""
% 4.11/1.00  --sat_gr_def                            false
% 4.11/1.00  --sat_epr_types                         true
% 4.11/1.00  --sat_non_cyclic_types                  false
% 4.11/1.00  --sat_finite_models                     false
% 4.11/1.00  --sat_fm_lemmas                         false
% 4.11/1.00  --sat_fm_prep                           false
% 4.11/1.00  --sat_fm_uc_incr                        true
% 4.11/1.00  --sat_out_model                         small
% 4.11/1.00  --sat_out_clauses                       false
% 4.11/1.00  
% 4.11/1.00  ------ QBF Options
% 4.11/1.00  
% 4.11/1.00  --qbf_mode                              false
% 4.11/1.00  --qbf_elim_univ                         false
% 4.11/1.00  --qbf_dom_inst                          none
% 4.11/1.00  --qbf_dom_pre_inst                      false
% 4.11/1.00  --qbf_sk_in                             false
% 4.11/1.00  --qbf_pred_elim                         true
% 4.11/1.00  --qbf_split                             512
% 4.11/1.00  
% 4.11/1.00  ------ BMC1 Options
% 4.11/1.00  
% 4.11/1.00  --bmc1_incremental                      false
% 4.11/1.00  --bmc1_axioms                           reachable_all
% 4.11/1.00  --bmc1_min_bound                        0
% 4.11/1.00  --bmc1_max_bound                        -1
% 4.11/1.00  --bmc1_max_bound_default                -1
% 4.11/1.00  --bmc1_symbol_reachability              true
% 4.11/1.00  --bmc1_property_lemmas                  false
% 4.11/1.00  --bmc1_k_induction                      false
% 4.11/1.00  --bmc1_non_equiv_states                 false
% 4.11/1.00  --bmc1_deadlock                         false
% 4.11/1.00  --bmc1_ucm                              false
% 4.11/1.00  --bmc1_add_unsat_core                   none
% 4.11/1.00  --bmc1_unsat_core_children              false
% 4.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/1.00  --bmc1_out_stat                         full
% 4.11/1.00  --bmc1_ground_init                      false
% 4.11/1.00  --bmc1_pre_inst_next_state              false
% 4.11/1.00  --bmc1_pre_inst_state                   false
% 4.11/1.00  --bmc1_pre_inst_reach_state             false
% 4.11/1.00  --bmc1_out_unsat_core                   false
% 4.11/1.00  --bmc1_aig_witness_out                  false
% 4.11/1.00  --bmc1_verbose                          false
% 4.11/1.00  --bmc1_dump_clauses_tptp                false
% 4.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.11/1.00  --bmc1_dump_file                        -
% 4.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.11/1.00  --bmc1_ucm_extend_mode                  1
% 4.11/1.00  --bmc1_ucm_init_mode                    2
% 4.11/1.00  --bmc1_ucm_cone_mode                    none
% 4.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.11/1.00  --bmc1_ucm_relax_model                  4
% 4.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/1.00  --bmc1_ucm_layered_model                none
% 4.11/1.00  --bmc1_ucm_max_lemma_size               10
% 4.11/1.00  
% 4.11/1.00  ------ AIG Options
% 4.11/1.00  
% 4.11/1.00  --aig_mode                              false
% 4.11/1.00  
% 4.11/1.00  ------ Instantiation Options
% 4.11/1.00  
% 4.11/1.00  --instantiation_flag                    true
% 4.11/1.00  --inst_sos_flag                         false
% 4.11/1.00  --inst_sos_phase                        true
% 4.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/1.00  --inst_lit_sel_side                     num_symb
% 4.11/1.00  --inst_solver_per_active                1400
% 4.11/1.00  --inst_solver_calls_frac                1.
% 4.11/1.00  --inst_passive_queue_type               priority_queues
% 4.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/1.00  --inst_passive_queues_freq              [25;2]
% 4.11/1.00  --inst_dismatching                      true
% 4.11/1.00  --inst_eager_unprocessed_to_passive     true
% 4.11/1.00  --inst_prop_sim_given                   true
% 4.11/1.00  --inst_prop_sim_new                     false
% 4.11/1.00  --inst_subs_new                         false
% 4.11/1.00  --inst_eq_res_simp                      false
% 4.11/1.00  --inst_subs_given                       false
% 4.11/1.00  --inst_orphan_elimination               true
% 4.11/1.00  --inst_learning_loop_flag               true
% 4.11/1.00  --inst_learning_start                   3000
% 4.11/1.00  --inst_learning_factor                  2
% 4.11/1.00  --inst_start_prop_sim_after_learn       3
% 4.11/1.00  --inst_sel_renew                        solver
% 4.11/1.00  --inst_lit_activity_flag                true
% 4.11/1.00  --inst_restr_to_given                   false
% 4.11/1.00  --inst_activity_threshold               500
% 4.11/1.00  --inst_out_proof                        true
% 4.11/1.00  
% 4.11/1.00  ------ Resolution Options
% 4.11/1.00  
% 4.11/1.00  --resolution_flag                       true
% 4.11/1.00  --res_lit_sel                           adaptive
% 4.11/1.00  --res_lit_sel_side                      none
% 4.11/1.00  --res_ordering                          kbo
% 4.11/1.00  --res_to_prop_solver                    active
% 4.11/1.00  --res_prop_simpl_new                    false
% 4.11/1.00  --res_prop_simpl_given                  true
% 4.11/1.00  --res_passive_queue_type                priority_queues
% 4.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/1.00  --res_passive_queues_freq               [15;5]
% 4.11/1.00  --res_forward_subs                      full
% 4.11/1.00  --res_backward_subs                     full
% 4.11/1.00  --res_forward_subs_resolution           true
% 4.11/1.00  --res_backward_subs_resolution          true
% 4.11/1.00  --res_orphan_elimination                true
% 4.11/1.00  --res_time_limit                        2.
% 4.11/1.00  --res_out_proof                         true
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Options
% 4.11/1.00  
% 4.11/1.00  --superposition_flag                    true
% 4.11/1.00  --sup_passive_queue_type                priority_queues
% 4.11/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/1.00  --sup_passive_queues_freq               [1;4]
% 4.11/1.00  --demod_completeness_check              fast
% 4.11/1.00  --demod_use_ground                      true
% 4.11/1.00  --sup_to_prop_solver                    passive
% 4.11/1.00  --sup_prop_simpl_new                    true
% 4.11/1.00  --sup_prop_simpl_given                  true
% 4.11/1.00  --sup_fun_splitting                     false
% 4.11/1.00  --sup_smt_interval                      50000
% 4.11/1.00  
% 4.11/1.00  ------ Superposition Simplification Setup
% 4.11/1.00  
% 4.11/1.00  --sup_indices_passive                   []
% 4.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_full_bw                           [BwDemod]
% 4.11/1.00  --sup_immed_triv                        [TrivRules]
% 4.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_immed_bw_main                     []
% 4.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/1.00  
% 4.11/1.00  ------ Combination Options
% 4.11/1.00  
% 4.11/1.00  --comb_res_mult                         3
% 4.11/1.00  --comb_sup_mult                         2
% 4.11/1.00  --comb_inst_mult                        10
% 4.11/1.00  
% 4.11/1.00  ------ Debug Options
% 4.11/1.00  
% 4.11/1.00  --dbg_backtrace                         false
% 4.11/1.00  --dbg_dump_prop_clauses                 false
% 4.11/1.00  --dbg_dump_prop_clauses_file            -
% 4.11/1.00  --dbg_out_stat                          false
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  ------ Proving...
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  % SZS status Theorem for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  fof(f2,axiom,(
% 4.11/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f54,plain,(
% 4.11/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.11/1.00    inference(cnf_transformation,[],[f2])).
% 4.11/1.00  
% 4.11/1.00  fof(f1,axiom,(
% 4.11/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f53,plain,(
% 4.11/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.11/1.00    inference(cnf_transformation,[],[f1])).
% 4.11/1.00  
% 4.11/1.00  fof(f17,conjecture,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f18,negated_conjecture,(
% 4.11/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 4.11/1.00    inference(negated_conjecture,[],[f17])).
% 4.11/1.00  
% 4.11/1.00  fof(f41,plain,(
% 4.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f18])).
% 4.11/1.00  
% 4.11/1.00  fof(f42,plain,(
% 4.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f41])).
% 4.11/1.00  
% 4.11/1.00  fof(f51,plain,(
% 4.11/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f50,plain,(
% 4.11/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f49,plain,(
% 4.11/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f48,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f47,plain,(
% 4.11/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f46,plain,(
% 4.11/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f45,plain,(
% 4.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 4.11/1.00    introduced(choice_axiom,[])).
% 4.11/1.00  
% 4.11/1.00  fof(f52,plain,(
% 4.11/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 4.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f51,f50,f49,f48,f47,f46,f45])).
% 4.11/1.00  
% 4.11/1.00  fof(f80,plain,(
% 4.11/1.00    m1_pre_topc(sK3,sK0)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f7,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f26,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f7])).
% 4.11/1.00  
% 4.11/1.00  fof(f59,plain,(
% 4.11/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f26])).
% 4.11/1.00  
% 4.11/1.00  fof(f73,plain,(
% 4.11/1.00    l1_pre_topc(sK0)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f6,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f25,plain,(
% 4.11/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f6])).
% 4.11/1.00  
% 4.11/1.00  fof(f58,plain,(
% 4.11/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f25])).
% 4.11/1.00  
% 4.11/1.00  fof(f5,axiom,(
% 4.11/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f24,plain,(
% 4.11/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f5])).
% 4.11/1.00  
% 4.11/1.00  fof(f57,plain,(
% 4.11/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f24])).
% 4.11/1.00  
% 4.11/1.00  fof(f11,axiom,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f32,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f11])).
% 4.11/1.00  
% 4.11/1.00  fof(f33,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f32])).
% 4.11/1.00  
% 4.11/1.00  fof(f64,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f33])).
% 4.11/1.00  
% 4.11/1.00  fof(f72,plain,(
% 4.11/1.00    v2_pre_topc(sK0)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f79,plain,(
% 4.11/1.00    ~v2_struct_0(sK3)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f4,axiom,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f22,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f4])).
% 4.11/1.00  
% 4.11/1.00  fof(f23,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.11/1.00    inference(flattening,[],[f22])).
% 4.11/1.00  
% 4.11/1.00  fof(f56,plain,(
% 4.11/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f23])).
% 4.11/1.00  
% 4.11/1.00  fof(f10,axiom,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f30,plain,(
% 4.11/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f10])).
% 4.11/1.00  
% 4.11/1.00  fof(f31,plain,(
% 4.11/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.11/1.00    inference(flattening,[],[f30])).
% 4.11/1.00  
% 4.11/1.00  fof(f63,plain,(
% 4.11/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f31])).
% 4.11/1.00  
% 4.11/1.00  fof(f88,plain,(
% 4.11/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f87,plain,(
% 4.11/1.00    sK5 = sK6),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f16,axiom,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f39,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f16])).
% 4.11/1.00  
% 4.11/1.00  fof(f40,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f39])).
% 4.11/1.00  
% 4.11/1.00  fof(f44,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.11/1.00    inference(nnf_transformation,[],[f40])).
% 4.11/1.00  
% 4.11/1.00  fof(f70,plain,(
% 4.11/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f44])).
% 4.11/1.00  
% 4.11/1.00  fof(f90,plain,(
% 4.11/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.11/1.00    inference(equality_resolution,[],[f70])).
% 4.11/1.00  
% 4.11/1.00  fof(f15,axiom,(
% 4.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f37,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f15])).
% 4.11/1.00  
% 4.11/1.00  fof(f38,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.11/1.00    inference(flattening,[],[f37])).
% 4.11/1.00  
% 4.11/1.00  fof(f68,plain,(
% 4.11/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f38])).
% 4.11/1.00  
% 4.11/1.00  fof(f76,plain,(
% 4.11/1.00    l1_pre_topc(sK1)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f71,plain,(
% 4.11/1.00    ~v2_struct_0(sK0)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f74,plain,(
% 4.11/1.00    ~v2_struct_0(sK1)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f75,plain,(
% 4.11/1.00    v2_pre_topc(sK1)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f77,plain,(
% 4.11/1.00    ~v2_struct_0(sK2)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f81,plain,(
% 4.11/1.00    v1_funct_1(sK4)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f85,plain,(
% 4.11/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f89,plain,(
% 4.11/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f86,plain,(
% 4.11/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f78,plain,(
% 4.11/1.00    m1_pre_topc(sK2,sK0)),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f13,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f35,plain,(
% 4.11/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f13])).
% 4.11/1.00  
% 4.11/1.00  fof(f66,plain,(
% 4.11/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f35])).
% 4.11/1.00  
% 4.11/1.00  fof(f84,plain,(
% 4.11/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f9,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f29,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f9])).
% 4.11/1.00  
% 4.11/1.00  fof(f43,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(nnf_transformation,[],[f29])).
% 4.11/1.00  
% 4.11/1.00  fof(f61,plain,(
% 4.11/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f43])).
% 4.11/1.00  
% 4.11/1.00  fof(f83,plain,(
% 4.11/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f82,plain,(
% 4.11/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 4.11/1.00    inference(cnf_transformation,[],[f52])).
% 4.11/1.00  
% 4.11/1.00  fof(f12,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f19,plain,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 4.11/1.00    inference(pure_predicate_removal,[],[f12])).
% 4.11/1.00  
% 4.11/1.00  fof(f34,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f19])).
% 4.11/1.00  
% 4.11/1.00  fof(f65,plain,(
% 4.11/1.00    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f34])).
% 4.11/1.00  
% 4.11/1.00  fof(f14,axiom,(
% 4.11/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f36,plain,(
% 4.11/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.11/1.00    inference(ennf_transformation,[],[f14])).
% 4.11/1.00  
% 4.11/1.00  fof(f67,plain,(
% 4.11/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f36])).
% 4.11/1.00  
% 4.11/1.00  fof(f3,axiom,(
% 4.11/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f20,plain,(
% 4.11/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 4.11/1.00    inference(ennf_transformation,[],[f3])).
% 4.11/1.00  
% 4.11/1.00  fof(f21,plain,(
% 4.11/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 4.11/1.00    inference(flattening,[],[f20])).
% 4.11/1.00  
% 4.11/1.00  fof(f55,plain,(
% 4.11/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f21])).
% 4.11/1.00  
% 4.11/1.00  fof(f8,axiom,(
% 4.11/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 4.11/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.11/1.00  
% 4.11/1.00  fof(f27,plain,(
% 4.11/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.11/1.00    inference(ennf_transformation,[],[f8])).
% 4.11/1.00  
% 4.11/1.00  fof(f28,plain,(
% 4.11/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.11/1.00    inference(flattening,[],[f27])).
% 4.11/1.00  
% 4.11/1.00  fof(f60,plain,(
% 4.11/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.11/1.00    inference(cnf_transformation,[],[f28])).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1,plain,
% 4.11/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f54]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_948,plain,
% 4.11/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_0,plain,
% 4.11/1.00      ( k2_subset_1(X0) = X0 ),
% 4.11/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_982,plain,
% 4.11/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_948,c_0]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_27,negated_conjecture,
% 4.11/1.00      ( m1_pre_topc(sK3,sK0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_925,plain,
% 4.11/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_6,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_943,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top
% 4.11/1.00      | l1_pre_topc(X0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2305,plain,
% 4.11/1.00      ( l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_925,c_943]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_34,negated_conjecture,
% 4.11/1.00      ( l1_pre_topc(sK0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_39,plain,
% 4.11/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1647,plain,
% 4.11/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 4.11/1.00      inference(resolution,[status(thm)],[c_6,c_27]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1648,plain,
% 4.11/1.00      ( l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3890,plain,
% 4.11/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2305,c_39,c_1648]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_5,plain,
% 4.11/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_944,plain,
% 4.11/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3895,plain,
% 4.11/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_3890,c_944]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4,plain,
% 4.11/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_945,plain,
% 4.11/1.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 4.11/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4034,plain,
% 4.11/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_3895,c_945]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_11,plain,
% 4.11/1.00      ( m1_connsp_2(X0,X1,X2)
% 4.11/1.00      | ~ v3_pre_topc(X0,X1)
% 4.11/1.00      | ~ r2_hidden(X2,X0)
% 4.11/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 4.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v2_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_939,plain,
% 4.11/1.00      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 4.11/1.00      | v3_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | r2_hidden(X2,X0) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 4.11/1.00      | v2_struct_0(X1) = iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top
% 4.11/1.00      | v2_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4049,plain,
% 4.11/1.00      ( m1_connsp_2(X0,sK3,X1) = iProver_top
% 4.11/1.00      | v3_pre_topc(X0,sK3) != iProver_top
% 4.11/1.00      | r2_hidden(X1,X0) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.11/1.00      | v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4034,c_939]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4072,plain,
% 4.11/1.00      ( m1_connsp_2(X0,sK3,X1) = iProver_top
% 4.11/1.00      | v3_pre_topc(X0,sK3) != iProver_top
% 4.11/1.00      | r2_hidden(X1,X0) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.11/1.00      | v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_4049,c_4034]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_35,negated_conjecture,
% 4.11/1.00      ( v2_pre_topc(sK0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_38,plain,
% 4.11/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_28,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK3) ),
% 4.11/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_45,plain,
% 4.11/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v2_pre_topc(X1)
% 4.11/1.00      | v2_pre_topc(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_946,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top
% 4.11/1.00      | v2_pre_topc(X1) != iProver_top
% 4.11/1.00      | v2_pre_topc(X0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2898,plain,
% 4.11/1.00      ( l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK0) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK3) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_925,c_946]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19189,plain,
% 4.11/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | r2_hidden(X1,X0) != iProver_top
% 4.11/1.00      | v3_pre_topc(X0,sK3) != iProver_top
% 4.11/1.00      | m1_connsp_2(X0,sK3,X1) = iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_4072,c_38,c_39,c_45,c_1648,c_2898]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19190,plain,
% 4.11/1.00      ( m1_connsp_2(X0,sK3,X1) = iProver_top
% 4.11/1.00      | v3_pre_topc(X0,sK3) != iProver_top
% 4.11/1.00      | r2_hidden(X1,X0) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_19189]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19200,plain,
% 4.11/1.00      ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
% 4.11/1.00      | v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
% 4.11/1.00      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_982,c_19190]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2945,plain,
% 4.11/1.00      ( m1_connsp_2(u1_struct_0(X0),X0,X1) = iProver_top
% 4.11/1.00      | v3_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 4.11/1.00      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.11/1.00      | v2_struct_0(X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X0) != iProver_top
% 4.11/1.00      | v2_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_982,c_939]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_10,plain,
% 4.11/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 4.11/1.00      | ~ l1_pre_topc(X0)
% 4.11/1.00      | ~ v2_pre_topc(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_73,plain,
% 4.11/1.00      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X0) != iProver_top
% 4.11/1.00      | v2_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_84,plain,
% 4.11/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_87,plain,
% 4.11/1.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 4.11/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_309,plain,
% 4.11/1.00      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 4.11/1.00      theory(equality) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1351,plain,
% 4.11/1.00      ( v3_pre_topc(X0,X1)
% 4.11/1.00      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 4.11/1.00      | X0 != k2_struct_0(X1) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_309]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1524,plain,
% 4.11/1.00      ( v3_pre_topc(u1_struct_0(X0),X0)
% 4.11/1.00      | ~ v3_pre_topc(k2_struct_0(X0),X0)
% 4.11/1.00      | u1_struct_0(X0) != k2_struct_0(X0) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_1351]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1525,plain,
% 4.11/1.00      ( u1_struct_0(X0) != k2_struct_0(X0)
% 4.11/1.00      | v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 4.11/1.00      | v3_pre_topc(k2_struct_0(X0),X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_9444,plain,
% 4.11/1.00      ( m1_connsp_2(u1_struct_0(X0),X0,X1) = iProver_top
% 4.11/1.00      | r2_hidden(X1,u1_struct_0(X0)) != iProver_top
% 4.11/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 4.11/1.00      | v2_struct_0(X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X0) != iProver_top
% 4.11/1.00      | v2_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2945,c_73,c_84,c_87,c_1525]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_9457,plain,
% 4.11/1.00      ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
% 4.11/1.00      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4034,c_9444]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_9492,plain,
% 4.11/1.00      ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
% 4.11/1.00      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_9457,c_4034]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19447,plain,
% 4.11/1.00      ( m1_connsp_2(k2_struct_0(sK3),sK3,X0) = iProver_top
% 4.11/1.00      | r2_hidden(X0,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k2_struct_0(sK3)) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_19200,c_38,c_39,c_45,c_1648,c_2898,c_9492]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19,negated_conjecture,
% 4.11/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 4.11/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_931,plain,
% 4.11/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_20,negated_conjecture,
% 4.11/1.00      ( sK5 = sK6 ),
% 4.11/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1003,plain,
% 4.11/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_931,c_20]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16,plain,
% 4.11/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 4.11/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 4.11/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 4.11/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 4.11/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 4.11/1.00      | ~ m1_pre_topc(X4,X5)
% 4.11/1.00      | ~ m1_pre_topc(X4,X0)
% 4.11/1.00      | ~ m1_pre_topc(X0,X5)
% 4.11/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 4.11/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 4.11/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.11/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 4.11/1.00      | ~ v1_funct_1(X2)
% 4.11/1.00      | v2_struct_0(X5)
% 4.11/1.00      | v2_struct_0(X1)
% 4.11/1.00      | v2_struct_0(X4)
% 4.11/1.00      | v2_struct_0(X0)
% 4.11/1.00      | ~ l1_pre_topc(X5)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v2_pre_topc(X5)
% 4.11/1.00      | ~ v2_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_934,plain,
% 4.11/1.00      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 4.11/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 4.11/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.11/1.00      | m1_connsp_2(X6,X0,X3) != iProver_top
% 4.11/1.00      | r1_tarski(X6,u1_struct_0(X4)) != iProver_top
% 4.11/1.00      | m1_pre_topc(X4,X5) != iProver_top
% 4.11/1.00      | m1_pre_topc(X4,X0) != iProver_top
% 4.11/1.00      | m1_pre_topc(X0,X5) != iProver_top
% 4.11/1.00      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 4.11/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.11/1.00      | m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v2_struct_0(X5) = iProver_top
% 4.11/1.00      | v2_struct_0(X1) = iProver_top
% 4.11/1.00      | v2_struct_0(X4) = iProver_top
% 4.11/1.00      | v2_struct_0(X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X5) != iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top
% 4.11/1.00      | v2_pre_topc(X5) != iProver_top
% 4.11/1.00      | v2_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_15,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | ~ m1_pre_topc(X2,X0)
% 4.11/1.00      | m1_pre_topc(X2,X1)
% 4.11/1.00      | ~ l1_pre_topc(X1)
% 4.11/1.00      | ~ v2_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_935,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 4.11/1.00      | m1_pre_topc(X2,X1) = iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top
% 4.11/1.00      | v2_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1153,plain,
% 4.11/1.00      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 4.11/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 4.11/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 4.11/1.00      | m1_connsp_2(X6,X0,X3) != iProver_top
% 4.11/1.00      | r1_tarski(X6,u1_struct_0(X4)) != iProver_top
% 4.11/1.00      | m1_pre_topc(X4,X0) != iProver_top
% 4.11/1.00      | m1_pre_topc(X0,X5) != iProver_top
% 4.11/1.00      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 4.11/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 4.11/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 4.11/1.00      | m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.11/1.00      | v1_funct_1(X2) != iProver_top
% 4.11/1.00      | v2_struct_0(X5) = iProver_top
% 4.11/1.00      | v2_struct_0(X1) = iProver_top
% 4.11/1.00      | v2_struct_0(X4) = iProver_top
% 4.11/1.00      | v2_struct_0(X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X5) != iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top
% 4.11/1.00      | v2_pre_topc(X5) != iProver_top
% 4.11/1.00      | v2_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(forward_subsumption_resolution,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_934,c_935]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3918,plain,
% 4.11/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 4.11/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 4.11/1.00      | m1_connsp_2(X0,sK3,sK5) != iProver_top
% 4.11/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 4.11/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK4) != iProver_top
% 4.11/1.00      | v2_struct_0(sK0) = iProver_top
% 4.11/1.00      | v2_struct_0(sK2) = iProver_top
% 4.11/1.00      | v2_struct_0(sK1) = iProver_top
% 4.11/1.00      | v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK1) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK0) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1003,c_1153]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_31,negated_conjecture,
% 4.11/1.00      ( l1_pre_topc(sK1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_921,plain,
% 4.11/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1895,plain,
% 4.11/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_921,c_944]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3313,plain,
% 4.11/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_1895,c_945]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3919,plain,
% 4.11/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 4.11/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
% 4.11/1.00      | m1_connsp_2(X0,sK3,sK5) != iProver_top
% 4.11/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 4.11/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 4.11/1.00      | v1_funct_1(sK4) != iProver_top
% 4.11/1.00      | v2_struct_0(sK0) = iProver_top
% 4.11/1.00      | v2_struct_0(sK2) = iProver_top
% 4.11/1.00      | v2_struct_0(sK1) = iProver_top
% 4.11/1.00      | v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK1) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK0) != iProver_top
% 4.11/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_3918,c_3313]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_36,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f71]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_37,plain,
% 4.11/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_33,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_40,plain,
% 4.11/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_32,negated_conjecture,
% 4.11/1.00      ( v2_pre_topc(sK1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_41,plain,
% 4.11/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_42,plain,
% 4.11/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_30,negated_conjecture,
% 4.11/1.00      ( ~ v2_struct_0(sK2) ),
% 4.11/1.00      inference(cnf_transformation,[],[f77]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_43,plain,
% 4.11/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_46,plain,
% 4.11/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_26,negated_conjecture,
% 4.11/1.00      ( v1_funct_1(sK4) ),
% 4.11/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_47,plain,
% 4.11/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_22,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f85]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_50,plain,
% 4.11/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_18,negated_conjecture,
% 4.11/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 4.11/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_53,plain,
% 4.11/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_21,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f86]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_930,plain,
% 4.11/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_977,plain,
% 4.11/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 4.11/1.00      inference(light_normalisation,[status(thm)],[c_930,c_20]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_29,negated_conjecture,
% 4.11/1.00      ( m1_pre_topc(sK2,sK0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f78]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1649,plain,
% 4.11/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 4.11/1.00      inference(resolution,[status(thm)],[c_6,c_29]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1650,plain,
% 4.11/1.00      ( l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_13,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 4.11/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_937,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_23,negated_conjecture,
% 4.11/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 4.11/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_9,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 4.11/1.00      | ~ l1_pre_topc(X0)
% 4.11/1.00      | ~ l1_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_262,plain,
% 4.11/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 4.11/1.00      | ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | ~ l1_pre_topc(X1) ),
% 4.11/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_6]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_263,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 4.11/1.00      | ~ l1_pre_topc(X1) ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_262]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_915,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1286,plain,
% 4.11/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 4.11/1.00      | m1_pre_topc(X0,sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_23,c_915]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2587,plain,
% 4.11/1.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 4.11/1.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_1286,c_39,c_1650]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2588,plain,
% 4.11/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 4.11/1.00      | m1_pre_topc(X0,sK3) = iProver_top ),
% 4.11/1.00      inference(renaming,[status(thm)],[c_2587]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2595,plain,
% 4.11/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_937,c_2588]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_24,negated_conjecture,
% 4.11/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 4.11/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_928,plain,
% 4.11/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3407,plain,
% 4.11/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3313,c_928]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_25,negated_conjecture,
% 4.11/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_927,plain,
% 4.11/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_3408,plain,
% 4.11/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_3313,c_927]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16715,plain,
% 4.11/1.00      ( m1_connsp_2(X0,sK3,sK5) != iProver_top
% 4.11/1.00      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_3919,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,
% 4.11/1.00                 c_47,c_50,c_53,c_977,c_1650,c_2595,c_3407,c_3408]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_923,plain,
% 4.11/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2306,plain,
% 4.11/1.00      ( l1_pre_topc(sK0) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_923,c_943]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4260,plain,
% 4.11/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_2306,c_39,c_1650]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4265,plain,
% 4.11/1.00      ( l1_struct_0(sK2) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4260,c_944]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4593,plain,
% 4.11/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4265,c_945]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16721,plain,
% 4.11/1.00      ( m1_connsp_2(X0,sK3,sK5) != iProver_top
% 4.11/1.00      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
% 4.11/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 4.11/1.00      inference(light_normalisation,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_16715,c_4034,c_4593]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16728,plain,
% 4.11/1.00      ( m1_connsp_2(k2_struct_0(sK3),sK3,sK5) != iProver_top
% 4.11/1.00      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_982,c_16721]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_12,plain,
% 4.11/1.00      ( ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 4.11/1.00      | ~ l1_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_938,plain,
% 4.11/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2728,plain,
% 4.11/1.00      ( m1_pre_topc(sK2,X0) != iProver_top
% 4.11/1.00      | m1_pre_topc(sK3,X0) = iProver_top
% 4.11/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_23,c_938]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2775,plain,
% 4.11/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_937,c_2728]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_14,plain,
% 4.11/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 4.11/1.00      | ~ m1_pre_topc(X0,X1)
% 4.11/1.00      | ~ l1_pre_topc(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_936,plain,
% 4.11/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 4.11/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 4.11/1.00      | l1_pre_topc(X1) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4046,plain,
% 4.11/1.00      ( r1_tarski(k2_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 4.11/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 4.11/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4034,c_936]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_7770,plain,
% 4.11/1.00      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 4.11/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 4.11/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4593,c_4046]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_16870,plain,
% 4.11/1.00      ( m1_connsp_2(k2_struct_0(sK3),sK3,sK5) != iProver_top ),
% 4.11/1.00      inference(global_propositional_subsumption,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_16728,c_39,c_1650,c_2775,c_7770]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_19456,plain,
% 4.11/1.00      ( r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 4.11/1.00      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_19447,c_16870]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_929,plain,
% 4.11/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4037,plain,
% 4.11/1.00      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(demodulation,[status(thm)],[c_4034,c_929]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_2,plain,
% 4.11/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 4.11/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_947,plain,
% 4.11/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.11/1.00      | m1_subset_1(X0,X1) != iProver_top
% 4.11/1.00      | v1_xboole_0(X1) = iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4257,plain,
% 4.11/1.00      ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top
% 4.11/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4037,c_947]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_7,plain,
% 4.11/1.00      ( v2_struct_0(X0)
% 4.11/1.00      | ~ l1_struct_0(X0)
% 4.11/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 4.11/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_942,plain,
% 4.11/1.00      ( v2_struct_0(X0) = iProver_top
% 4.11/1.00      | l1_struct_0(X0) != iProver_top
% 4.11/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_4047,plain,
% 4.11/1.00      ( v2_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_struct_0(sK3) != iProver_top
% 4.11/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 4.11/1.00      inference(superposition,[status(thm)],[c_4034,c_942]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1597,plain,
% 4.11/1.00      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 4.11/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(c_1598,plain,
% 4.11/1.00      ( l1_struct_0(sK3) = iProver_top
% 4.11/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 4.11/1.00      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 4.11/1.00  
% 4.11/1.00  cnf(contradiction,plain,
% 4.11/1.00      ( $false ),
% 4.11/1.00      inference(minisat,
% 4.11/1.00                [status(thm)],
% 4.11/1.00                [c_19456,c_4257,c_4047,c_4037,c_1648,c_1598,c_45,c_39]) ).
% 4.11/1.00  
% 4.11/1.00  
% 4.11/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/1.00  
% 4.11/1.00  ------                               Statistics
% 4.11/1.00  
% 4.11/1.00  ------ Selected
% 4.11/1.00  
% 4.11/1.00  total_time:                             0.504
% 4.11/1.00  
%------------------------------------------------------------------------------
