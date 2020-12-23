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
% DateTime   : Thu Dec  3 12:23:06 EST 2020

% Result     : Theorem 8.19s
% Output     : CNFRefutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  241 (28714 expanded)
%              Number of clauses        :  166 (5443 expanded)
%              Number of leaves         :   18 (13929 expanded)
%              Depth                    :   34
%              Number of atoms          : 1721 (453675 expanded)
%              Number of equality atoms :  791 (42945 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f32,f40,f39,f38,f37,f36,f35,f34])).

fof(f72,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f43])).

fof(f9,axiom,(
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
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f69,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_335,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_880,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_15,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_334,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_898,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_880,c_334])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_325,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_889,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_327,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_887,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_330,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_884,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_344,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X3_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_871,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_2154,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_871])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2379,plain,
    ( l1_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_35,c_36,c_37,c_42,c_43])).

cnf(c_2380,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2379])).

cnf(c_2386,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_887,c_2380])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_345,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_870,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_2015,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_870])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2244,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2015,c_32,c_33,c_34,c_35,c_36,c_37,c_42,c_43])).

cnf(c_2245,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | m1_pre_topc(X0_50,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2244])).

cnf(c_2250,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_887,c_2245])).

cnf(c_2390,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2386,c_2250])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_57,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_59,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_2763,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2390,c_32,c_33,c_34,c_41,c_59])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_343,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_872,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_2155,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X4_50)) = k3_tmap_1(X5_50,X1_50,X0_50,X4_50,k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51))
    | v1_funct_2(X0_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X4_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X5_50) != iProver_top
    | m1_pre_topc(X4_50,X5_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X5_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X5_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X5_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_871])).

cnf(c_4572,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2155])).

cnf(c_4713,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4572,c_2763])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_873,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_2766,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_873])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_341,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_874,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_2020,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_874])).

cnf(c_2372,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2020,c_35,c_36,c_37,c_42,c_43])).

cnf(c_2373,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2372])).

cnf(c_2767,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2373])).

cnf(c_2765,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_872])).

cnf(c_3181,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2765,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,c_44,c_59])).

cnf(c_3185,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_871])).

cnf(c_5467,plain,
    ( m1_pre_topc(sK3,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4713,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,c_44,c_59,c_2766,c_2767,c_3185])).

cnf(c_5468,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5467])).

cnf(c_5475,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_889,c_5468])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_331,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_883,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_2053,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X4_50)) = k2_tmap_1(X0_50,X1_50,k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),X4_50)
    | v1_funct_2(X0_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X4_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_870])).

cnf(c_3390,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),X0_50)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2053])).

cnf(c_3519,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3390,c_2763])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_346,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1246,plain,
    ( ~ m1_pre_topc(sK3,X0_50)
    | ~ l1_pre_topc(X0_50)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1247,plain,
    ( m1_pre_topc(sK3,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_1249,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_347,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1339,plain,
    ( ~ m1_pre_topc(sK3,X0_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X0_50)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_1340,plain,
    ( m1_pre_topc(sK3,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_1342,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_3187,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_870])).

cnf(c_3669,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
    | m1_pre_topc(X0_50,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3519,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,c_43,c_44,c_59,c_1249,c_1342,c_2766,c_2767,c_3187])).

cnf(c_3675,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_883,c_3669])).

cnf(c_5477,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5475,c_3675])).

cnf(c_45,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5487,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5477,c_32,c_33,c_34,c_41,c_45])).

cnf(c_0,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_349,plain,
    ( r2_funct_2(X0_52,X1_52,X0_51,X0_51)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_866,plain,
    ( r2_funct_2(X0_52,X1_52,X0_51,X0_51) = iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_2055,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_866])).

cnf(c_2768,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2055])).

cnf(c_2770,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2768,c_2763])).

cnf(c_3282,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2770,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,c_44,c_59,c_2766,c_2767])).

cnf(c_11,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_338,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k2_tmap_1(X2_50,X1_50,X1_51,X0_50))
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k2_tmap_1(X2_50,X1_50,X1_51,X3_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X3_50,X0_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X3_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X1_51)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_877,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k2_tmap_1(X2_50,X1_50,X1_51,X0_50)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k2_tmap_1(X2_50,X1_50,X1_51,X3_50)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_3286,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_50)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_877])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_337,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | m1_pre_topc(X2_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_878,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1664,plain,
    ( m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(X0_50,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_887,c_878])).

cnf(c_1950,plain,
    ( m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(X0_50,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_33,c_34])).

cnf(c_7947,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_50)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3286,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,c_43,c_44,c_59,c_1664,c_2765,c_2766,c_2767])).

cnf(c_7948,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_50)) = iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | v2_struct_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_7947])).

cnf(c_7953,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5487,c_7948])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8315,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7953,c_38,c_45])).

cnf(c_5489,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5487,c_872])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6478,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5489,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_41,c_42,c_43,c_44,c_59,c_2765,c_2766,c_2767])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_348,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
    | ~ v1_funct_2(X1_51,X0_52,X1_52)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X1_51)
    | ~ v1_funct_1(X0_51)
    | X0_51 = X1_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_867,plain,
    ( X0_51 = X1_51
    | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_6485,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6478,c_867])).

cnf(c_5490,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5487,c_873])).

cnf(c_2052,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X4_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X5_50,X4_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) != iProver_top
    | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
    inference(superposition,[status(thm)],[c_872,c_874])).

cnf(c_382,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_385,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_2875,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_pre_topc(X5_50,X4_50) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X3_50,X4_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2052,c_382,c_385])).

cnf(c_2876,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X4_50) != iProver_top
    | m1_pre_topc(X2_50,X4_50) != iProver_top
    | m1_pre_topc(X5_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X4_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | l1_pre_topc(X4_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X4_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X2_50,X5_50,k3_tmap_1(X4_50,X1_50,X0_50,X2_50,X0_51))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2875])).

cnf(c_2882,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2876])).

cnf(c_3186,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_874])).

cnf(c_3380,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2882,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,c_44,c_59,c_2766,c_2767,c_3186])).

cnf(c_3381,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3380])).

cnf(c_5495,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5487,c_3381])).

cnf(c_6789,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6485,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_41,c_42,c_43,c_44,c_59,c_2765,c_2766,c_2767,c_5490,c_5495])).

cnf(c_6790,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6789])).

cnf(c_8320,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8315,c_6790])).

cnf(c_2387,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_889,c_2380])).

cnf(c_2251,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_889,c_2245])).

cnf(c_2389,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2387,c_2251])).

cnf(c_2709,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2389,c_32,c_33,c_34,c_39,c_59])).

cnf(c_2711,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2709,c_872])).

cnf(c_2712,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2709,c_873])).

cnf(c_2713,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2709,c_2373])).

cnf(c_12808,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8320,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_42,c_43,c_44,c_59,c_2711,c_2712,c_2713])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_339,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
    | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_876,plain,
    ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
    | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_12825,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12808,c_876])).

cnf(c_23942,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12825,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_40,c_41,c_42,c_43,c_44,c_45,c_59,c_1249,c_1342,c_2765,c_2766,c_2767])).

cnf(c_23943,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23942])).

cnf(c_23949,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_23943])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_332,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_882,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_897,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_882,c_334])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_49,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23949,c_897,c_49,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 8.19/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.19/1.47  
% 8.19/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.19/1.47  
% 8.19/1.47  ------  iProver source info
% 8.19/1.47  
% 8.19/1.47  git: date: 2020-06-30 10:37:57 +0100
% 8.19/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.19/1.47  git: non_committed_changes: false
% 8.19/1.47  git: last_make_outside_of_git: false
% 8.19/1.47  
% 8.19/1.47  ------ 
% 8.19/1.47  
% 8.19/1.47  ------ Input Options
% 8.19/1.47  
% 8.19/1.47  --out_options                           all
% 8.19/1.47  --tptp_safe_out                         true
% 8.19/1.47  --problem_path                          ""
% 8.19/1.47  --include_path                          ""
% 8.19/1.47  --clausifier                            res/vclausify_rel
% 8.19/1.47  --clausifier_options                    ""
% 8.19/1.47  --stdin                                 false
% 8.19/1.47  --stats_out                             all
% 8.19/1.47  
% 8.19/1.47  ------ General Options
% 8.19/1.47  
% 8.19/1.47  --fof                                   false
% 8.19/1.47  --time_out_real                         305.
% 8.19/1.47  --time_out_virtual                      -1.
% 8.19/1.47  --symbol_type_check                     false
% 8.19/1.47  --clausify_out                          false
% 8.19/1.47  --sig_cnt_out                           false
% 8.19/1.47  --trig_cnt_out                          false
% 8.19/1.47  --trig_cnt_out_tolerance                1.
% 8.19/1.47  --trig_cnt_out_sk_spl                   false
% 8.19/1.47  --abstr_cl_out                          false
% 8.19/1.47  
% 8.19/1.47  ------ Global Options
% 8.19/1.47  
% 8.19/1.47  --schedule                              default
% 8.19/1.47  --add_important_lit                     false
% 8.19/1.47  --prop_solver_per_cl                    1000
% 8.19/1.47  --min_unsat_core                        false
% 8.19/1.47  --soft_assumptions                      false
% 8.19/1.47  --soft_lemma_size                       3
% 8.19/1.47  --prop_impl_unit_size                   0
% 8.19/1.47  --prop_impl_unit                        []
% 8.19/1.47  --share_sel_clauses                     true
% 8.19/1.47  --reset_solvers                         false
% 8.19/1.47  --bc_imp_inh                            [conj_cone]
% 8.19/1.47  --conj_cone_tolerance                   3.
% 8.19/1.47  --extra_neg_conj                        none
% 8.19/1.47  --large_theory_mode                     true
% 8.19/1.47  --prolific_symb_bound                   200
% 8.19/1.47  --lt_threshold                          2000
% 8.19/1.47  --clause_weak_htbl                      true
% 8.19/1.47  --gc_record_bc_elim                     false
% 8.19/1.47  
% 8.19/1.47  ------ Preprocessing Options
% 8.19/1.47  
% 8.19/1.47  --preprocessing_flag                    true
% 8.19/1.47  --time_out_prep_mult                    0.1
% 8.19/1.47  --splitting_mode                        input
% 8.19/1.47  --splitting_grd                         true
% 8.19/1.47  --splitting_cvd                         false
% 8.19/1.47  --splitting_cvd_svl                     false
% 8.19/1.47  --splitting_nvd                         32
% 8.19/1.47  --sub_typing                            true
% 8.19/1.47  --prep_gs_sim                           true
% 8.19/1.47  --prep_unflatten                        true
% 8.19/1.47  --prep_res_sim                          true
% 8.19/1.47  --prep_upred                            true
% 8.19/1.47  --prep_sem_filter                       exhaustive
% 8.19/1.47  --prep_sem_filter_out                   false
% 8.19/1.47  --pred_elim                             true
% 8.19/1.47  --res_sim_input                         true
% 8.19/1.47  --eq_ax_congr_red                       true
% 8.19/1.47  --pure_diseq_elim                       true
% 8.19/1.47  --brand_transform                       false
% 8.19/1.47  --non_eq_to_eq                          false
% 8.19/1.47  --prep_def_merge                        true
% 8.19/1.47  --prep_def_merge_prop_impl              false
% 8.19/1.47  --prep_def_merge_mbd                    true
% 8.19/1.47  --prep_def_merge_tr_red                 false
% 8.19/1.47  --prep_def_merge_tr_cl                  false
% 8.19/1.47  --smt_preprocessing                     true
% 8.19/1.47  --smt_ac_axioms                         fast
% 8.19/1.47  --preprocessed_out                      false
% 8.19/1.47  --preprocessed_stats                    false
% 8.19/1.47  
% 8.19/1.47  ------ Abstraction refinement Options
% 8.19/1.47  
% 8.19/1.47  --abstr_ref                             []
% 8.19/1.47  --abstr_ref_prep                        false
% 8.19/1.47  --abstr_ref_until_sat                   false
% 8.19/1.47  --abstr_ref_sig_restrict                funpre
% 8.19/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 8.19/1.47  --abstr_ref_under                       []
% 8.19/1.47  
% 8.19/1.47  ------ SAT Options
% 8.19/1.47  
% 8.19/1.47  --sat_mode                              false
% 8.19/1.47  --sat_fm_restart_options                ""
% 8.19/1.47  --sat_gr_def                            false
% 8.19/1.47  --sat_epr_types                         true
% 8.19/1.47  --sat_non_cyclic_types                  false
% 8.19/1.47  --sat_finite_models                     false
% 8.19/1.47  --sat_fm_lemmas                         false
% 8.19/1.47  --sat_fm_prep                           false
% 8.19/1.47  --sat_fm_uc_incr                        true
% 8.19/1.47  --sat_out_model                         small
% 8.19/1.47  --sat_out_clauses                       false
% 8.19/1.47  
% 8.19/1.47  ------ QBF Options
% 8.19/1.47  
% 8.19/1.47  --qbf_mode                              false
% 8.19/1.47  --qbf_elim_univ                         false
% 8.19/1.47  --qbf_dom_inst                          none
% 8.19/1.47  --qbf_dom_pre_inst                      false
% 8.19/1.47  --qbf_sk_in                             false
% 8.19/1.47  --qbf_pred_elim                         true
% 8.19/1.47  --qbf_split                             512
% 8.19/1.47  
% 8.19/1.47  ------ BMC1 Options
% 8.19/1.47  
% 8.19/1.47  --bmc1_incremental                      false
% 8.19/1.47  --bmc1_axioms                           reachable_all
% 8.19/1.47  --bmc1_min_bound                        0
% 8.19/1.47  --bmc1_max_bound                        -1
% 8.19/1.47  --bmc1_max_bound_default                -1
% 8.19/1.47  --bmc1_symbol_reachability              true
% 8.19/1.47  --bmc1_property_lemmas                  false
% 8.19/1.47  --bmc1_k_induction                      false
% 8.19/1.47  --bmc1_non_equiv_states                 false
% 8.19/1.47  --bmc1_deadlock                         false
% 8.19/1.47  --bmc1_ucm                              false
% 8.19/1.47  --bmc1_add_unsat_core                   none
% 8.19/1.47  --bmc1_unsat_core_children              false
% 8.19/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 8.19/1.47  --bmc1_out_stat                         full
% 8.19/1.47  --bmc1_ground_init                      false
% 8.19/1.47  --bmc1_pre_inst_next_state              false
% 8.19/1.47  --bmc1_pre_inst_state                   false
% 8.19/1.47  --bmc1_pre_inst_reach_state             false
% 8.19/1.47  --bmc1_out_unsat_core                   false
% 8.19/1.47  --bmc1_aig_witness_out                  false
% 8.19/1.47  --bmc1_verbose                          false
% 8.19/1.47  --bmc1_dump_clauses_tptp                false
% 8.19/1.47  --bmc1_dump_unsat_core_tptp             false
% 8.19/1.47  --bmc1_dump_file                        -
% 8.19/1.47  --bmc1_ucm_expand_uc_limit              128
% 8.19/1.47  --bmc1_ucm_n_expand_iterations          6
% 8.19/1.47  --bmc1_ucm_extend_mode                  1
% 8.19/1.47  --bmc1_ucm_init_mode                    2
% 8.19/1.47  --bmc1_ucm_cone_mode                    none
% 8.19/1.47  --bmc1_ucm_reduced_relation_type        0
% 8.19/1.47  --bmc1_ucm_relax_model                  4
% 8.19/1.47  --bmc1_ucm_full_tr_after_sat            true
% 8.19/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 8.19/1.47  --bmc1_ucm_layered_model                none
% 8.19/1.47  --bmc1_ucm_max_lemma_size               10
% 8.19/1.47  
% 8.19/1.47  ------ AIG Options
% 8.19/1.47  
% 8.19/1.47  --aig_mode                              false
% 8.19/1.47  
% 8.19/1.47  ------ Instantiation Options
% 8.19/1.47  
% 8.19/1.47  --instantiation_flag                    true
% 8.19/1.47  --inst_sos_flag                         true
% 8.19/1.47  --inst_sos_phase                        true
% 8.19/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.19/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.19/1.47  --inst_lit_sel_side                     num_symb
% 8.19/1.47  --inst_solver_per_active                1400
% 8.19/1.47  --inst_solver_calls_frac                1.
% 8.19/1.47  --inst_passive_queue_type               priority_queues
% 8.19/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.19/1.47  --inst_passive_queues_freq              [25;2]
% 8.19/1.47  --inst_dismatching                      true
% 8.19/1.47  --inst_eager_unprocessed_to_passive     true
% 8.19/1.47  --inst_prop_sim_given                   true
% 8.19/1.47  --inst_prop_sim_new                     false
% 8.19/1.47  --inst_subs_new                         false
% 8.19/1.47  --inst_eq_res_simp                      false
% 8.19/1.47  --inst_subs_given                       false
% 8.19/1.47  --inst_orphan_elimination               true
% 8.19/1.47  --inst_learning_loop_flag               true
% 8.19/1.47  --inst_learning_start                   3000
% 8.19/1.47  --inst_learning_factor                  2
% 8.19/1.47  --inst_start_prop_sim_after_learn       3
% 8.19/1.47  --inst_sel_renew                        solver
% 8.19/1.47  --inst_lit_activity_flag                true
% 8.19/1.47  --inst_restr_to_given                   false
% 8.19/1.47  --inst_activity_threshold               500
% 8.19/1.47  --inst_out_proof                        true
% 8.19/1.47  
% 8.19/1.47  ------ Resolution Options
% 8.19/1.47  
% 8.19/1.47  --resolution_flag                       true
% 8.19/1.47  --res_lit_sel                           adaptive
% 8.19/1.47  --res_lit_sel_side                      none
% 8.19/1.47  --res_ordering                          kbo
% 8.19/1.47  --res_to_prop_solver                    active
% 8.19/1.47  --res_prop_simpl_new                    false
% 8.19/1.47  --res_prop_simpl_given                  true
% 8.19/1.47  --res_passive_queue_type                priority_queues
% 8.19/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.19/1.47  --res_passive_queues_freq               [15;5]
% 8.19/1.47  --res_forward_subs                      full
% 8.19/1.47  --res_backward_subs                     full
% 8.19/1.47  --res_forward_subs_resolution           true
% 8.19/1.47  --res_backward_subs_resolution          true
% 8.19/1.47  --res_orphan_elimination                true
% 8.19/1.47  --res_time_limit                        2.
% 8.19/1.47  --res_out_proof                         true
% 8.19/1.47  
% 8.19/1.47  ------ Superposition Options
% 8.19/1.47  
% 8.19/1.47  --superposition_flag                    true
% 8.19/1.47  --sup_passive_queue_type                priority_queues
% 8.19/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.19/1.47  --sup_passive_queues_freq               [8;1;4]
% 8.19/1.47  --demod_completeness_check              fast
% 8.19/1.47  --demod_use_ground                      true
% 8.19/1.47  --sup_to_prop_solver                    passive
% 8.19/1.47  --sup_prop_simpl_new                    true
% 8.19/1.47  --sup_prop_simpl_given                  true
% 8.19/1.47  --sup_fun_splitting                     true
% 8.19/1.47  --sup_smt_interval                      50000
% 8.19/1.47  
% 8.19/1.47  ------ Superposition Simplification Setup
% 8.19/1.47  
% 8.19/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.19/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.19/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.19/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 8.19/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.19/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.19/1.47  --sup_immed_triv                        [TrivRules]
% 8.19/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.47  --sup_immed_bw_main                     []
% 8.19/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.19/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 8.19/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.47  --sup_input_bw                          []
% 8.19/1.47  
% 8.19/1.47  ------ Combination Options
% 8.19/1.47  
% 8.19/1.47  --comb_res_mult                         3
% 8.19/1.47  --comb_sup_mult                         2
% 8.19/1.47  --comb_inst_mult                        10
% 8.19/1.47  
% 8.19/1.47  ------ Debug Options
% 8.19/1.47  
% 8.19/1.47  --dbg_backtrace                         false
% 8.19/1.47  --dbg_dump_prop_clauses                 false
% 8.19/1.47  --dbg_dump_prop_clauses_file            -
% 8.19/1.47  --dbg_out_stat                          false
% 8.19/1.47  ------ Parsing...
% 8.19/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.19/1.47  
% 8.19/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.19/1.47  
% 8.19/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.19/1.47  
% 8.19/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.19/1.47  ------ Proving...
% 8.19/1.47  ------ Problem Properties 
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  clauses                                 32
% 8.19/1.47  conjectures                             19
% 8.19/1.47  EPR                                     17
% 8.19/1.47  Horn                                    25
% 8.19/1.47  unary                                   19
% 8.19/1.47  binary                                  1
% 8.19/1.47  lits                                    139
% 8.19/1.47  lits eq                                 4
% 8.19/1.47  fd_pure                                 0
% 8.19/1.47  fd_pseudo                               0
% 8.19/1.47  fd_cond                                 0
% 8.19/1.47  fd_pseudo_cond                          1
% 8.19/1.47  AC symbols                              0
% 8.19/1.47  
% 8.19/1.47  ------ Schedule dynamic 5 is on 
% 8.19/1.47  
% 8.19/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  ------ 
% 8.19/1.47  Current options:
% 8.19/1.47  ------ 
% 8.19/1.47  
% 8.19/1.47  ------ Input Options
% 8.19/1.47  
% 8.19/1.47  --out_options                           all
% 8.19/1.47  --tptp_safe_out                         true
% 8.19/1.47  --problem_path                          ""
% 8.19/1.47  --include_path                          ""
% 8.19/1.47  --clausifier                            res/vclausify_rel
% 8.19/1.47  --clausifier_options                    ""
% 8.19/1.47  --stdin                                 false
% 8.19/1.47  --stats_out                             all
% 8.19/1.47  
% 8.19/1.47  ------ General Options
% 8.19/1.47  
% 8.19/1.47  --fof                                   false
% 8.19/1.47  --time_out_real                         305.
% 8.19/1.47  --time_out_virtual                      -1.
% 8.19/1.47  --symbol_type_check                     false
% 8.19/1.47  --clausify_out                          false
% 8.19/1.47  --sig_cnt_out                           false
% 8.19/1.47  --trig_cnt_out                          false
% 8.19/1.47  --trig_cnt_out_tolerance                1.
% 8.19/1.47  --trig_cnt_out_sk_spl                   false
% 8.19/1.47  --abstr_cl_out                          false
% 8.19/1.47  
% 8.19/1.47  ------ Global Options
% 8.19/1.47  
% 8.19/1.47  --schedule                              default
% 8.19/1.47  --add_important_lit                     false
% 8.19/1.47  --prop_solver_per_cl                    1000
% 8.19/1.47  --min_unsat_core                        false
% 8.19/1.47  --soft_assumptions                      false
% 8.19/1.47  --soft_lemma_size                       3
% 8.19/1.47  --prop_impl_unit_size                   0
% 8.19/1.47  --prop_impl_unit                        []
% 8.19/1.47  --share_sel_clauses                     true
% 8.19/1.47  --reset_solvers                         false
% 8.19/1.47  --bc_imp_inh                            [conj_cone]
% 8.19/1.47  --conj_cone_tolerance                   3.
% 8.19/1.47  --extra_neg_conj                        none
% 8.19/1.47  --large_theory_mode                     true
% 8.19/1.47  --prolific_symb_bound                   200
% 8.19/1.47  --lt_threshold                          2000
% 8.19/1.47  --clause_weak_htbl                      true
% 8.19/1.47  --gc_record_bc_elim                     false
% 8.19/1.47  
% 8.19/1.47  ------ Preprocessing Options
% 8.19/1.47  
% 8.19/1.47  --preprocessing_flag                    true
% 8.19/1.47  --time_out_prep_mult                    0.1
% 8.19/1.47  --splitting_mode                        input
% 8.19/1.47  --splitting_grd                         true
% 8.19/1.47  --splitting_cvd                         false
% 8.19/1.47  --splitting_cvd_svl                     false
% 8.19/1.47  --splitting_nvd                         32
% 8.19/1.47  --sub_typing                            true
% 8.19/1.47  --prep_gs_sim                           true
% 8.19/1.47  --prep_unflatten                        true
% 8.19/1.47  --prep_res_sim                          true
% 8.19/1.47  --prep_upred                            true
% 8.19/1.47  --prep_sem_filter                       exhaustive
% 8.19/1.47  --prep_sem_filter_out                   false
% 8.19/1.47  --pred_elim                             true
% 8.19/1.47  --res_sim_input                         true
% 8.19/1.47  --eq_ax_congr_red                       true
% 8.19/1.47  --pure_diseq_elim                       true
% 8.19/1.47  --brand_transform                       false
% 8.19/1.47  --non_eq_to_eq                          false
% 8.19/1.47  --prep_def_merge                        true
% 8.19/1.47  --prep_def_merge_prop_impl              false
% 8.19/1.47  --prep_def_merge_mbd                    true
% 8.19/1.47  --prep_def_merge_tr_red                 false
% 8.19/1.47  --prep_def_merge_tr_cl                  false
% 8.19/1.47  --smt_preprocessing                     true
% 8.19/1.47  --smt_ac_axioms                         fast
% 8.19/1.47  --preprocessed_out                      false
% 8.19/1.47  --preprocessed_stats                    false
% 8.19/1.47  
% 8.19/1.47  ------ Abstraction refinement Options
% 8.19/1.47  
% 8.19/1.47  --abstr_ref                             []
% 8.19/1.47  --abstr_ref_prep                        false
% 8.19/1.47  --abstr_ref_until_sat                   false
% 8.19/1.47  --abstr_ref_sig_restrict                funpre
% 8.19/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 8.19/1.47  --abstr_ref_under                       []
% 8.19/1.47  
% 8.19/1.47  ------ SAT Options
% 8.19/1.47  
% 8.19/1.47  --sat_mode                              false
% 8.19/1.47  --sat_fm_restart_options                ""
% 8.19/1.47  --sat_gr_def                            false
% 8.19/1.47  --sat_epr_types                         true
% 8.19/1.47  --sat_non_cyclic_types                  false
% 8.19/1.47  --sat_finite_models                     false
% 8.19/1.47  --sat_fm_lemmas                         false
% 8.19/1.47  --sat_fm_prep                           false
% 8.19/1.47  --sat_fm_uc_incr                        true
% 8.19/1.47  --sat_out_model                         small
% 8.19/1.47  --sat_out_clauses                       false
% 8.19/1.47  
% 8.19/1.47  ------ QBF Options
% 8.19/1.47  
% 8.19/1.47  --qbf_mode                              false
% 8.19/1.47  --qbf_elim_univ                         false
% 8.19/1.47  --qbf_dom_inst                          none
% 8.19/1.47  --qbf_dom_pre_inst                      false
% 8.19/1.47  --qbf_sk_in                             false
% 8.19/1.47  --qbf_pred_elim                         true
% 8.19/1.47  --qbf_split                             512
% 8.19/1.47  
% 8.19/1.47  ------ BMC1 Options
% 8.19/1.47  
% 8.19/1.47  --bmc1_incremental                      false
% 8.19/1.47  --bmc1_axioms                           reachable_all
% 8.19/1.47  --bmc1_min_bound                        0
% 8.19/1.47  --bmc1_max_bound                        -1
% 8.19/1.47  --bmc1_max_bound_default                -1
% 8.19/1.47  --bmc1_symbol_reachability              true
% 8.19/1.47  --bmc1_property_lemmas                  false
% 8.19/1.47  --bmc1_k_induction                      false
% 8.19/1.47  --bmc1_non_equiv_states                 false
% 8.19/1.47  --bmc1_deadlock                         false
% 8.19/1.47  --bmc1_ucm                              false
% 8.19/1.47  --bmc1_add_unsat_core                   none
% 8.19/1.47  --bmc1_unsat_core_children              false
% 8.19/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 8.19/1.47  --bmc1_out_stat                         full
% 8.19/1.47  --bmc1_ground_init                      false
% 8.19/1.47  --bmc1_pre_inst_next_state              false
% 8.19/1.47  --bmc1_pre_inst_state                   false
% 8.19/1.47  --bmc1_pre_inst_reach_state             false
% 8.19/1.47  --bmc1_out_unsat_core                   false
% 8.19/1.47  --bmc1_aig_witness_out                  false
% 8.19/1.47  --bmc1_verbose                          false
% 8.19/1.47  --bmc1_dump_clauses_tptp                false
% 8.19/1.47  --bmc1_dump_unsat_core_tptp             false
% 8.19/1.47  --bmc1_dump_file                        -
% 8.19/1.47  --bmc1_ucm_expand_uc_limit              128
% 8.19/1.47  --bmc1_ucm_n_expand_iterations          6
% 8.19/1.47  --bmc1_ucm_extend_mode                  1
% 8.19/1.47  --bmc1_ucm_init_mode                    2
% 8.19/1.47  --bmc1_ucm_cone_mode                    none
% 8.19/1.47  --bmc1_ucm_reduced_relation_type        0
% 8.19/1.47  --bmc1_ucm_relax_model                  4
% 8.19/1.47  --bmc1_ucm_full_tr_after_sat            true
% 8.19/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 8.19/1.47  --bmc1_ucm_layered_model                none
% 8.19/1.47  --bmc1_ucm_max_lemma_size               10
% 8.19/1.47  
% 8.19/1.47  ------ AIG Options
% 8.19/1.47  
% 8.19/1.47  --aig_mode                              false
% 8.19/1.47  
% 8.19/1.47  ------ Instantiation Options
% 8.19/1.47  
% 8.19/1.47  --instantiation_flag                    true
% 8.19/1.47  --inst_sos_flag                         true
% 8.19/1.47  --inst_sos_phase                        true
% 8.19/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.19/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.19/1.47  --inst_lit_sel_side                     none
% 8.19/1.47  --inst_solver_per_active                1400
% 8.19/1.47  --inst_solver_calls_frac                1.
% 8.19/1.47  --inst_passive_queue_type               priority_queues
% 8.19/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.19/1.47  --inst_passive_queues_freq              [25;2]
% 8.19/1.47  --inst_dismatching                      true
% 8.19/1.47  --inst_eager_unprocessed_to_passive     true
% 8.19/1.47  --inst_prop_sim_given                   true
% 8.19/1.47  --inst_prop_sim_new                     false
% 8.19/1.47  --inst_subs_new                         false
% 8.19/1.47  --inst_eq_res_simp                      false
% 8.19/1.47  --inst_subs_given                       false
% 8.19/1.47  --inst_orphan_elimination               true
% 8.19/1.47  --inst_learning_loop_flag               true
% 8.19/1.47  --inst_learning_start                   3000
% 8.19/1.47  --inst_learning_factor                  2
% 8.19/1.47  --inst_start_prop_sim_after_learn       3
% 8.19/1.47  --inst_sel_renew                        solver
% 8.19/1.47  --inst_lit_activity_flag                true
% 8.19/1.47  --inst_restr_to_given                   false
% 8.19/1.47  --inst_activity_threshold               500
% 8.19/1.47  --inst_out_proof                        true
% 8.19/1.47  
% 8.19/1.47  ------ Resolution Options
% 8.19/1.47  
% 8.19/1.47  --resolution_flag                       false
% 8.19/1.47  --res_lit_sel                           adaptive
% 8.19/1.47  --res_lit_sel_side                      none
% 8.19/1.47  --res_ordering                          kbo
% 8.19/1.47  --res_to_prop_solver                    active
% 8.19/1.47  --res_prop_simpl_new                    false
% 8.19/1.47  --res_prop_simpl_given                  true
% 8.19/1.47  --res_passive_queue_type                priority_queues
% 8.19/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.19/1.47  --res_passive_queues_freq               [15;5]
% 8.19/1.47  --res_forward_subs                      full
% 8.19/1.47  --res_backward_subs                     full
% 8.19/1.47  --res_forward_subs_resolution           true
% 8.19/1.47  --res_backward_subs_resolution          true
% 8.19/1.47  --res_orphan_elimination                true
% 8.19/1.47  --res_time_limit                        2.
% 8.19/1.47  --res_out_proof                         true
% 8.19/1.47  
% 8.19/1.47  ------ Superposition Options
% 8.19/1.47  
% 8.19/1.47  --superposition_flag                    true
% 8.19/1.47  --sup_passive_queue_type                priority_queues
% 8.19/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.19/1.47  --sup_passive_queues_freq               [8;1;4]
% 8.19/1.47  --demod_completeness_check              fast
% 8.19/1.47  --demod_use_ground                      true
% 8.19/1.47  --sup_to_prop_solver                    passive
% 8.19/1.47  --sup_prop_simpl_new                    true
% 8.19/1.47  --sup_prop_simpl_given                  true
% 8.19/1.47  --sup_fun_splitting                     true
% 8.19/1.47  --sup_smt_interval                      50000
% 8.19/1.47  
% 8.19/1.47  ------ Superposition Simplification Setup
% 8.19/1.47  
% 8.19/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.19/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.19/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.19/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.19/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 8.19/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.19/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.19/1.47  --sup_immed_triv                        [TrivRules]
% 8.19/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.47  --sup_immed_bw_main                     []
% 8.19/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.19/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 8.19/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.19/1.47  --sup_input_bw                          []
% 8.19/1.47  
% 8.19/1.47  ------ Combination Options
% 8.19/1.47  
% 8.19/1.47  --comb_res_mult                         3
% 8.19/1.47  --comb_sup_mult                         2
% 8.19/1.47  --comb_inst_mult                        10
% 8.19/1.47  
% 8.19/1.47  ------ Debug Options
% 8.19/1.47  
% 8.19/1.47  --dbg_backtrace                         false
% 8.19/1.47  --dbg_dump_prop_clauses                 false
% 8.19/1.47  --dbg_dump_prop_clauses_file            -
% 8.19/1.47  --dbg_out_stat                          false
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  ------ Proving...
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  % SZS status Theorem for theBenchmark.p
% 8.19/1.47  
% 8.19/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 8.19/1.47  
% 8.19/1.47  fof(f11,conjecture,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f12,negated_conjecture,(
% 8.19/1.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 8.19/1.47    inference(negated_conjecture,[],[f11])).
% 8.19/1.47  
% 8.19/1.47  fof(f31,plain,(
% 8.19/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f12])).
% 8.19/1.47  
% 8.19/1.47  fof(f32,plain,(
% 8.19/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.19/1.47    inference(flattening,[],[f31])).
% 8.19/1.47  
% 8.19/1.47  fof(f40,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f39,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f38,plain,(
% 8.19/1.47    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f37,plain,(
% 8.19/1.47    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f36,plain,(
% 8.19/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f35,plain,(
% 8.19/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f34,plain,(
% 8.19/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 8.19/1.47    introduced(choice_axiom,[])).
% 8.19/1.47  
% 8.19/1.47  fof(f41,plain,(
% 8.19/1.47    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 8.19/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f32,f40,f39,f38,f37,f36,f35,f34])).
% 8.19/1.47  
% 8.19/1.47  fof(f72,plain,(
% 8.19/1.47    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f71,plain,(
% 8.19/1.47    sK5 = sK6),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f62,plain,(
% 8.19/1.47    m1_pre_topc(sK2,sK0)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f64,plain,(
% 8.19/1.47    m1_pre_topc(sK3,sK0)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f67,plain,(
% 8.19/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f5,axiom,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f20,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f5])).
% 8.19/1.47  
% 8.19/1.47  fof(f21,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.19/1.47    inference(flattening,[],[f20])).
% 8.19/1.47  
% 8.19/1.47  fof(f47,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f21])).
% 8.19/1.47  
% 8.19/1.47  fof(f58,plain,(
% 8.19/1.47    ~v2_struct_0(sK1)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f59,plain,(
% 8.19/1.47    v2_pre_topc(sK1)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f60,plain,(
% 8.19/1.47    l1_pre_topc(sK1)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f65,plain,(
% 8.19/1.47    v1_funct_1(sK4)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f66,plain,(
% 8.19/1.47    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f4,axiom,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f18,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f4])).
% 8.19/1.47  
% 8.19/1.47  fof(f19,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.19/1.47    inference(flattening,[],[f18])).
% 8.19/1.47  
% 8.19/1.47  fof(f46,plain,(
% 8.19/1.47    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f19])).
% 8.19/1.47  
% 8.19/1.47  fof(f55,plain,(
% 8.19/1.47    ~v2_struct_0(sK0)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f56,plain,(
% 8.19/1.47    v2_pre_topc(sK0)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f57,plain,(
% 8.19/1.47    l1_pre_topc(sK0)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f7,axiom,(
% 8.19/1.47    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f24,plain,(
% 8.19/1.47    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 8.19/1.47    inference(ennf_transformation,[],[f7])).
% 8.19/1.47  
% 8.19/1.47  fof(f51,plain,(
% 8.19/1.47    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f24])).
% 8.19/1.47  
% 8.19/1.47  fof(f6,axiom,(
% 8.19/1.47    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f22,plain,(
% 8.19/1.47    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f6])).
% 8.19/1.47  
% 8.19/1.47  fof(f23,plain,(
% 8.19/1.47    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.19/1.47    inference(flattening,[],[f22])).
% 8.19/1.47  
% 8.19/1.47  fof(f50,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f23])).
% 8.19/1.47  
% 8.19/1.47  fof(f49,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f23])).
% 8.19/1.47  
% 8.19/1.47  fof(f48,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f23])).
% 8.19/1.47  
% 8.19/1.47  fof(f68,plain,(
% 8.19/1.47    m1_pre_topc(sK2,sK3)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f63,plain,(
% 8.19/1.47    ~v2_struct_0(sK3)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f3,axiom,(
% 8.19/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f17,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.19/1.47    inference(ennf_transformation,[],[f3])).
% 8.19/1.47  
% 8.19/1.47  fof(f45,plain,(
% 8.19/1.47    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f17])).
% 8.19/1.47  
% 8.19/1.47  fof(f2,axiom,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f15,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f2])).
% 8.19/1.47  
% 8.19/1.47  fof(f16,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.19/1.47    inference(flattening,[],[f15])).
% 8.19/1.47  
% 8.19/1.47  fof(f44,plain,(
% 8.19/1.47    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f16])).
% 8.19/1.47  
% 8.19/1.47  fof(f1,axiom,(
% 8.19/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f13,plain,(
% 8.19/1.47    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.19/1.47    inference(ennf_transformation,[],[f1])).
% 8.19/1.47  
% 8.19/1.47  fof(f14,plain,(
% 8.19/1.47    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.19/1.47    inference(flattening,[],[f13])).
% 8.19/1.47  
% 8.19/1.47  fof(f33,plain,(
% 8.19/1.47    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.19/1.47    inference(nnf_transformation,[],[f14])).
% 8.19/1.47  
% 8.19/1.47  fof(f43,plain,(
% 8.19/1.47    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f33])).
% 8.19/1.47  
% 8.19/1.47  fof(f74,plain,(
% 8.19/1.47    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.19/1.47    inference(equality_resolution,[],[f43])).
% 8.19/1.47  
% 8.19/1.47  fof(f9,axiom,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f27,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f9])).
% 8.19/1.47  
% 8.19/1.47  fof(f28,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.19/1.47    inference(flattening,[],[f27])).
% 8.19/1.47  
% 8.19/1.47  fof(f53,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f28])).
% 8.19/1.47  
% 8.19/1.47  fof(f10,axiom,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f29,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f10])).
% 8.19/1.47  
% 8.19/1.47  fof(f30,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.19/1.47    inference(flattening,[],[f29])).
% 8.19/1.47  
% 8.19/1.47  fof(f54,plain,(
% 8.19/1.47    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f30])).
% 8.19/1.47  
% 8.19/1.47  fof(f61,plain,(
% 8.19/1.47    ~v2_struct_0(sK2)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f42,plain,(
% 8.19/1.47    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f33])).
% 8.19/1.47  
% 8.19/1.47  fof(f8,axiom,(
% 8.19/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 8.19/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.19/1.47  
% 8.19/1.47  fof(f25,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.19/1.47    inference(ennf_transformation,[],[f8])).
% 8.19/1.47  
% 8.19/1.47  fof(f26,plain,(
% 8.19/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.19/1.47    inference(flattening,[],[f25])).
% 8.19/1.47  
% 8.19/1.47  fof(f52,plain,(
% 8.19/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(cnf_transformation,[],[f26])).
% 8.19/1.47  
% 8.19/1.47  fof(f75,plain,(
% 8.19/1.47    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.19/1.47    inference(equality_resolution,[],[f52])).
% 8.19/1.47  
% 8.19/1.47  fof(f69,plain,(
% 8.19/1.47    m1_subset_1(sK5,u1_struct_0(sK3))),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f73,plain,(
% 8.19/1.47    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  fof(f70,plain,(
% 8.19/1.47    m1_subset_1(sK6,u1_struct_0(sK2))),
% 8.19/1.47    inference(cnf_transformation,[],[f41])).
% 8.19/1.47  
% 8.19/1.47  cnf(c_14,negated_conjecture,
% 8.19/1.47      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 8.19/1.47      inference(cnf_transformation,[],[f72]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_335,negated_conjecture,
% 8.19/1.47      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_14]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_880,plain,
% 8.19/1.47      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_15,negated_conjecture,
% 8.19/1.47      ( sK5 = sK6 ),
% 8.19/1.47      inference(cnf_transformation,[],[f71]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_334,negated_conjecture,
% 8.19/1.47      ( sK5 = sK6 ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_15]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_898,plain,
% 8.19/1.47      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_880,c_334]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_24,negated_conjecture,
% 8.19/1.47      ( m1_pre_topc(sK2,sK0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f62]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_325,negated_conjecture,
% 8.19/1.47      ( m1_pre_topc(sK2,sK0) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_24]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_889,plain,
% 8.19/1.47      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_22,negated_conjecture,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f64]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_327,negated_conjecture,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_22]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_887,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_19,negated_conjecture,
% 8.19/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 8.19/1.47      inference(cnf_transformation,[],[f67]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_330,negated_conjecture,
% 8.19/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_19]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_884,plain,
% 8.19/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.19/1.47      | ~ m1_pre_topc(X3,X4)
% 8.19/1.47      | ~ m1_pre_topc(X3,X1)
% 8.19/1.47      | ~ m1_pre_topc(X1,X4)
% 8.19/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.19/1.47      | v2_struct_0(X4)
% 8.19/1.47      | v2_struct_0(X2)
% 8.19/1.47      | ~ l1_pre_topc(X4)
% 8.19/1.47      | ~ l1_pre_topc(X2)
% 8.19/1.47      | ~ v2_pre_topc(X4)
% 8.19/1.47      | ~ v2_pre_topc(X2)
% 8.19/1.47      | ~ v1_funct_1(X0)
% 8.19/1.47      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f47]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_344,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X2_50,X0_50)
% 8.19/1.47      | ~ m1_pre_topc(X0_50,X3_50)
% 8.19/1.47      | ~ m1_pre_topc(X2_50,X3_50)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X3_50)
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X3_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X3_50)
% 8.19/1.47      | ~ v1_funct_1(X0_51)
% 8.19/1.47      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_5]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_871,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X3_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X3_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X3_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2154,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_884,c_871]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_28,negated_conjecture,
% 8.19/1.47      ( ~ v2_struct_0(sK1) ),
% 8.19/1.47      inference(cnf_transformation,[],[f58]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_35,plain,
% 8.19/1.47      ( v2_struct_0(sK1) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_27,negated_conjecture,
% 8.19/1.47      ( v2_pre_topc(sK1) ),
% 8.19/1.47      inference(cnf_transformation,[],[f59]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_36,plain,
% 8.19/1.47      ( v2_pre_topc(sK1) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_26,negated_conjecture,
% 8.19/1.47      ( l1_pre_topc(sK1) ),
% 8.19/1.47      inference(cnf_transformation,[],[f60]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_37,plain,
% 8.19/1.47      ( l1_pre_topc(sK1) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_21,negated_conjecture,
% 8.19/1.47      ( v1_funct_1(sK4) ),
% 8.19/1.47      inference(cnf_transformation,[],[f65]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_42,plain,
% 8.19/1.47      ( v1_funct_1(sK4) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_20,negated_conjecture,
% 8.19/1.47      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 8.19/1.47      inference(cnf_transformation,[],[f66]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_43,plain,
% 8.19/1.47      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2379,plain,
% 8.19/1.47      ( l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2154,c_35,c_36,c_37,c_42,c_43]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2380,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_2379]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2386,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_887,c_2380]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_4,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.19/1.47      | ~ m1_pre_topc(X3,X1)
% 8.19/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.19/1.47      | v2_struct_0(X1)
% 8.19/1.47      | v2_struct_0(X2)
% 8.19/1.47      | ~ l1_pre_topc(X1)
% 8.19/1.47      | ~ l1_pre_topc(X2)
% 8.19/1.47      | ~ v2_pre_topc(X1)
% 8.19/1.47      | ~ v2_pre_topc(X2)
% 8.19/1.47      | ~ v1_funct_1(X0)
% 8.19/1.47      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 8.19/1.47      inference(cnf_transformation,[],[f46]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_345,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X2_50,X0_50)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | v2_struct_0(X0_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X0_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X0_50)
% 8.19/1.47      | ~ v1_funct_1(X0_51)
% 8.19/1.47      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_4]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_870,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X0_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2015,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_884,c_870]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_31,negated_conjecture,
% 8.19/1.47      ( ~ v2_struct_0(sK0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f55]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_32,plain,
% 8.19/1.47      ( v2_struct_0(sK0) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_30,negated_conjecture,
% 8.19/1.47      ( v2_pre_topc(sK0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f56]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_33,plain,
% 8.19/1.47      ( v2_pre_topc(sK0) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_29,negated_conjecture,
% 8.19/1.47      ( l1_pre_topc(sK0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f57]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_34,plain,
% 8.19/1.47      ( l1_pre_topc(sK0) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2244,plain,
% 8.19/1.47      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 8.19/1.47      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2015,c_32,c_33,c_34,c_35,c_36,c_37,c_42,c_43]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2245,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) != iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_2244]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2250,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_887,c_2245]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2390,plain,
% 8.19/1.47      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_2386,c_2250]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_41,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_9,plain,
% 8.19/1.47      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f51]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_57,plain,
% 8.19/1.47      ( m1_pre_topc(X0,X0) = iProver_top
% 8.19/1.47      | l1_pre_topc(X0) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_59,plain,
% 8.19/1.47      ( m1_pre_topc(sK0,sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(instantiation,[status(thm)],[c_57]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2763,plain,
% 8.19/1.47      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2390,c_32,c_33,c_34,c_41,c_59]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_6,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.19/1.47      | ~ m1_pre_topc(X3,X4)
% 8.19/1.47      | ~ m1_pre_topc(X1,X4)
% 8.19/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.19/1.47      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 8.19/1.47      | v2_struct_0(X4)
% 8.19/1.47      | v2_struct_0(X2)
% 8.19/1.47      | ~ l1_pre_topc(X4)
% 8.19/1.47      | ~ l1_pre_topc(X2)
% 8.19/1.47      | ~ v2_pre_topc(X4)
% 8.19/1.47      | ~ v2_pre_topc(X2)
% 8.19/1.47      | ~ v1_funct_1(X0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f50]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_343,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X0_50,X2_50)
% 8.19/1.47      | ~ m1_pre_topc(X3_50,X2_50)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X2_50)
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X2_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X2_50)
% 8.19/1.47      | ~ v1_funct_1(X0_51) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_6]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_872,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) = iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2155,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X4_50)) = k3_tmap_1(X5_50,X1_50,X0_50,X4_50,k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51))
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X4_50,X0_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X5_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X4_50,X5_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X5_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X5_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X5_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_872,c_871]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_4572,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_2155]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_4713,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_4572,c_2763]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_44,plain,
% 8.19/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_7,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 8.19/1.47      | ~ m1_pre_topc(X4,X3)
% 8.19/1.47      | ~ m1_pre_topc(X1,X3)
% 8.19/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.19/1.47      | v2_struct_0(X3)
% 8.19/1.47      | v2_struct_0(X2)
% 8.19/1.47      | ~ l1_pre_topc(X3)
% 8.19/1.47      | ~ l1_pre_topc(X2)
% 8.19/1.47      | ~ v2_pre_topc(X3)
% 8.19/1.47      | ~ v2_pre_topc(X2)
% 8.19/1.47      | ~ v1_funct_1(X0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f49]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_342,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X3_50,X2_50)
% 8.19/1.47      | ~ m1_pre_topc(X0_50,X2_50)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | v2_struct_0(X2_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X2_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X2_50)
% 8.19/1.47      | ~ v1_funct_1(X0_51) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_7]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_873,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2766,plain,
% 8.19/1.47      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_873]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_8,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.19/1.47      | ~ m1_pre_topc(X3,X4)
% 8.19/1.47      | ~ m1_pre_topc(X1,X4)
% 8.19/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.19/1.47      | v2_struct_0(X4)
% 8.19/1.47      | v2_struct_0(X2)
% 8.19/1.47      | ~ l1_pre_topc(X4)
% 8.19/1.47      | ~ l1_pre_topc(X2)
% 8.19/1.47      | ~ v2_pre_topc(X4)
% 8.19/1.47      | ~ v2_pre_topc(X2)
% 8.19/1.47      | ~ v1_funct_1(X0)
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 8.19/1.47      inference(cnf_transformation,[],[f48]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_341,plain,
% 8.19/1.47      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X0_50,X2_50)
% 8.19/1.47      | ~ m1_pre_topc(X3_50,X2_50)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X2_50)
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X2_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X2_50)
% 8.19/1.47      | ~ v1_funct_1(X0_51)
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_8]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_874,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2020,plain,
% 8.19/1.47      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_884,c_874]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2372,plain,
% 8.19/1.47      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2020,c_35,c_36,c_37,c_42,c_43]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2373,plain,
% 8.19/1.47      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_2372]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2767,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_2373]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2765,plain,
% 8.19/1.47      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_872]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3181,plain,
% 8.19/1.47      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2765,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,
% 8.19/1.47                 c_44,c_59]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3185,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_3181,c_871]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5467,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_4713,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,
% 8.19/1.47                 c_44,c_59,c_2766,c_2767,c_3185]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5468,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_5467]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5475,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_889,c_5468]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_18,negated_conjecture,
% 8.19/1.47      ( m1_pre_topc(sK2,sK3) ),
% 8.19/1.47      inference(cnf_transformation,[],[f68]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_331,negated_conjecture,
% 8.19/1.47      ( m1_pre_topc(sK2,sK3) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_18]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_883,plain,
% 8.19/1.47      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2053,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X4_50)) = k2_tmap_1(X0_50,X1_50,k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),X4_50)
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X4_50,X0_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X0_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_872,c_870]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3390,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),X0_50)
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK3) = iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK3) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK3) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_2053]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3519,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK3) = iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK3) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK3) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_3390,c_2763]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_23,negated_conjecture,
% 8.19/1.47      ( ~ v2_struct_0(sK3) ),
% 8.19/1.47      inference(cnf_transformation,[],[f63]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_40,plain,
% 8.19/1.47      ( v2_struct_0(sK3) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3,plain,
% 8.19/1.47      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f45]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_346,plain,
% 8.19/1.47      ( ~ m1_pre_topc(X0_50,X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | l1_pre_topc(X0_50) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_3]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1246,plain,
% 8.19/1.47      ( ~ m1_pre_topc(sK3,X0_50)
% 8.19/1.47      | ~ l1_pre_topc(X0_50)
% 8.19/1.47      | l1_pre_topc(sK3) ),
% 8.19/1.47      inference(instantiation,[status(thm)],[c_346]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1247,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,X0_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK3) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1249,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK3) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(instantiation,[status(thm)],[c_1247]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2,plain,
% 8.19/1.47      ( ~ m1_pre_topc(X0,X1)
% 8.19/1.47      | ~ l1_pre_topc(X1)
% 8.19/1.47      | ~ v2_pre_topc(X1)
% 8.19/1.47      | v2_pre_topc(X0) ),
% 8.19/1.47      inference(cnf_transformation,[],[f44]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_347,plain,
% 8.19/1.47      ( ~ m1_pre_topc(X0_50,X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | v2_pre_topc(X0_50) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_2]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1339,plain,
% 8.19/1.47      ( ~ m1_pre_topc(sK3,X0_50)
% 8.19/1.47      | ~ l1_pre_topc(X0_50)
% 8.19/1.47      | ~ v2_pre_topc(X0_50)
% 8.19/1.47      | v2_pre_topc(sK3) ),
% 8.19/1.47      inference(instantiation,[status(thm)],[c_347]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1340,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,X0_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK3) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_1339]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1342,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK3) = iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(instantiation,[status(thm)],[c_1340]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3187,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | v2_struct_0(sK3) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK3) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK3) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_3181,c_870]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3669,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_3519,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,
% 8.19/1.47                 c_43,c_44,c_59,c_1249,c_1342,c_2766,c_2767,c_3187]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3675,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_883,c_3669]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5477,plain,
% 8.19/1.47      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_5475,c_3675]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_45,plain,
% 8.19/1.47      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5487,plain,
% 8.19/1.47      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_5477,c_32,c_33,c_34,c_41,c_45]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_0,plain,
% 8.19/1.47      ( r2_funct_2(X0,X1,X2,X2)
% 8.19/1.47      | ~ v1_funct_2(X2,X0,X1)
% 8.19/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.19/1.47      | ~ v1_funct_1(X2) ),
% 8.19/1.47      inference(cnf_transformation,[],[f74]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_349,plain,
% 8.19/1.47      ( r2_funct_2(X0_52,X1_52,X0_51,X0_51)
% 8.19/1.47      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 8.19/1.47      | ~ v1_funct_1(X0_51) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_0]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_866,plain,
% 8.19/1.47      ( r2_funct_2(X0_52,X1_52,X0_51,X0_51) = iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2055,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) = iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51),u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X3_50,X0_50,X0_51)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_872,c_866]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2768,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_2055]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2770,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_2768,c_2763]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3282,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2770,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,
% 8.19/1.47                 c_44,c_59,c_2766,c_2767]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_11,plain,
% 8.19/1.47      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 8.19/1.47      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 8.19/1.47      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.19/1.47      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 8.19/1.47      | ~ m1_pre_topc(X5,X3)
% 8.19/1.47      | ~ m1_pre_topc(X5,X0)
% 8.19/1.47      | ~ m1_pre_topc(X0,X3)
% 8.19/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.19/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 8.19/1.47      | v2_struct_0(X3)
% 8.19/1.47      | v2_struct_0(X1)
% 8.19/1.47      | v2_struct_0(X5)
% 8.19/1.47      | v2_struct_0(X0)
% 8.19/1.47      | ~ l1_pre_topc(X3)
% 8.19/1.47      | ~ l1_pre_topc(X1)
% 8.19/1.47      | ~ v2_pre_topc(X3)
% 8.19/1.47      | ~ v2_pre_topc(X1)
% 8.19/1.47      | ~ v1_funct_1(X4)
% 8.19/1.47      | ~ v1_funct_1(X2) ),
% 8.19/1.47      inference(cnf_transformation,[],[f53]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_338,plain,
% 8.19/1.47      ( ~ r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k2_tmap_1(X2_50,X1_50,X1_51,X0_50))
% 8.19/1.47      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k2_tmap_1(X2_50,X1_50,X1_51,X3_50))
% 8.19/1.47      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X3_50,X2_50)
% 8.19/1.47      | ~ m1_pre_topc(X3_50,X0_50)
% 8.19/1.47      | ~ m1_pre_topc(X0_50,X2_50)
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X3_50)
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | v2_struct_0(X0_50)
% 8.19/1.47      | v2_struct_0(X2_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X2_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X2_50)
% 8.19/1.47      | ~ v1_funct_1(X1_51)
% 8.19/1.47      | ~ v1_funct_1(X0_51) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_11]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_877,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k2_tmap_1(X2_50,X1_50,X1_51,X0_50)) != iProver_top
% 8.19/1.47      | r2_funct_2(u1_struct_0(X3_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k2_tmap_1(X2_50,X1_50,X1_51,X3_50)) = iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X3_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X0_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(X1_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3286,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_50)) = iProver_top
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X0_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK3) = iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_3282,c_877]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_12,plain,
% 8.19/1.47      ( ~ m1_pre_topc(X0,X1)
% 8.19/1.47      | ~ m1_pre_topc(X2,X0)
% 8.19/1.47      | m1_pre_topc(X2,X1)
% 8.19/1.47      | ~ l1_pre_topc(X1)
% 8.19/1.47      | ~ v2_pre_topc(X1) ),
% 8.19/1.47      inference(cnf_transformation,[],[f54]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_337,plain,
% 8.19/1.47      ( ~ m1_pre_topc(X0_50,X1_50)
% 8.19/1.47      | ~ m1_pre_topc(X2_50,X0_50)
% 8.19/1.47      | m1_pre_topc(X2_50,X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_12]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_878,plain,
% 8.19/1.47      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1664,plain,
% 8.19/1.47      ( m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_887,c_878]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1950,plain,
% 8.19/1.47      ( m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK0) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_1664,c_33,c_34]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_7947,plain,
% 8.19/1.47      ( v2_struct_0(X0_50) = iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_50)) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_3286,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_42,
% 8.19/1.47                 c_43,c_44,c_59,c_1664,c_2765,c_2766,c_2767]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_7948,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,X0_50)) = iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,sK3) != iProver_top
% 8.19/1.47      | v2_struct_0(X0_50) = iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_7947]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_7953,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.19/1.47      | v2_struct_0(sK2) = iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_5487,c_7948]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_25,negated_conjecture,
% 8.19/1.47      ( ~ v2_struct_0(sK2) ),
% 8.19/1.47      inference(cnf_transformation,[],[f61]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_38,plain,
% 8.19/1.47      ( v2_struct_0(sK2) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_8315,plain,
% 8.19/1.47      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_7953,c_38,c_45]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5489,plain,
% 8.19/1.47      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_5487,c_872]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_39,plain,
% 8.19/1.47      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_6478,plain,
% 8.19/1.47      ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_5489,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_41,c_42,
% 8.19/1.47                 c_43,c_44,c_59,c_2765,c_2766,c_2767]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_1,plain,
% 8.19/1.47      ( ~ r2_funct_2(X0,X1,X2,X3)
% 8.19/1.47      | ~ v1_funct_2(X3,X0,X1)
% 8.19/1.47      | ~ v1_funct_2(X2,X0,X1)
% 8.19/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.19/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.19/1.47      | ~ v1_funct_1(X3)
% 8.19/1.47      | ~ v1_funct_1(X2)
% 8.19/1.47      | X2 = X3 ),
% 8.19/1.47      inference(cnf_transformation,[],[f42]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_348,plain,
% 8.19/1.47      ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
% 8.19/1.47      | ~ v1_funct_2(X1_51,X0_52,X1_52)
% 8.19/1.47      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 8.19/1.47      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 8.19/1.47      | ~ v1_funct_1(X1_51)
% 8.19/1.47      | ~ v1_funct_1(X0_51)
% 8.19/1.47      | X0_51 = X1_51 ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_1]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_867,plain,
% 8.19/1.47      ( X0_51 = X1_51
% 8.19/1.47      | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 8.19/1.47      | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 8.19/1.47      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(X1_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_6485,plain,
% 8.19/1.47      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
% 8.19/1.47      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_6478,c_867]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5490,plain,
% 8.19/1.47      ( v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_5487,c_873]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2052,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X4_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X5_50,X4_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X4_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X4_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X4_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_872,c_874]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_382,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_385,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2875,plain,
% 8.19/1.47      ( v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v2_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X4_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X2_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X4_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X4_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | m1_pre_topc(X5_50,X4_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X3_50,X4_50) != iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X4_50,X1_50,X3_50,X5_50,k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51))) = iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2052,c_382,c_385]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2876,plain,
% 8.19/1.47      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X4_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X4_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(X5_50,X3_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X3_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X4_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X3_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X4_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X3_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X4_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X3_50,X1_50,X2_50,X5_50,k3_tmap_1(X4_50,X1_50,X0_50,X2_50,X0_51))) = iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_2875]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2882,plain,
% 8.19/1.47      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2763,c_2876]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3186,plain,
% 8.19/1.47      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_3181,c_874]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3380,plain,
% 8.19/1.47      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2882,c_32,c_33,c_34,c_35,c_36,c_37,c_41,c_42,c_43,
% 8.19/1.47                 c_44,c_59,c_2766,c_2767,c_3186]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_3381,plain,
% 8.19/1.47      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK3,X1_50) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_3380]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_5495,plain,
% 8.19/1.47      ( m1_pre_topc(sK3,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) = iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_5487,c_3381]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_6789,plain,
% 8.19/1.47      ( v1_funct_1(X0_51) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
% 8.19/1.47      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_6485,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_41,c_42,
% 8.19/1.47                 c_43,c_44,c_59,c_2765,c_2766,c_2767,c_5490,c_5495]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_6790,plain,
% 8.19/1.47      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
% 8.19/1.47      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_6789]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_8320,plain,
% 8.19/1.47      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_8315,c_6790]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2387,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_889,c_2380]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2251,plain,
% 8.19/1.47      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_889,c_2245]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2389,plain,
% 8.19/1.47      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_2387,c_2251]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2709,plain,
% 8.19/1.47      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_2389,c_32,c_33,c_34,c_39,c_59]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2711,plain,
% 8.19/1.47      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2709,c_872]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2712,plain,
% 8.19/1.47      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 8.19/1.47      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(sK4) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2709,c_873]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_2713,plain,
% 8.19/1.47      ( m1_pre_topc(sK0,sK0) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK0) != iProver_top
% 8.19/1.47      | v2_struct_0(sK0) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK0) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_2709,c_2373]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_12808,plain,
% 8.19/1.47      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_8320,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_42,c_43,
% 8.19/1.47                 c_44,c_59,c_2711,c_2712,c_2713]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_10,plain,
% 8.19/1.47      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 8.19/1.47      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.19/1.47      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.19/1.47      | ~ m1_pre_topc(X4,X0)
% 8.19/1.47      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.19/1.47      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.19/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.19/1.47      | v2_struct_0(X1)
% 8.19/1.47      | v2_struct_0(X0)
% 8.19/1.47      | v2_struct_0(X4)
% 8.19/1.47      | ~ l1_pre_topc(X1)
% 8.19/1.47      | ~ l1_pre_topc(X0)
% 8.19/1.47      | ~ v2_pre_topc(X1)
% 8.19/1.47      | ~ v2_pre_topc(X0)
% 8.19/1.47      | ~ v1_funct_1(X2) ),
% 8.19/1.47      inference(cnf_transformation,[],[f75]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_339,plain,
% 8.19/1.47      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
% 8.19/1.47      | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51)
% 8.19/1.47      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 8.19/1.47      | ~ m1_pre_topc(X2_50,X0_50)
% 8.19/1.47      | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
% 8.19/1.47      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 8.19/1.47      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 8.19/1.47      | v2_struct_0(X1_50)
% 8.19/1.47      | v2_struct_0(X0_50)
% 8.19/1.47      | v2_struct_0(X2_50)
% 8.19/1.47      | ~ l1_pre_topc(X1_50)
% 8.19/1.47      | ~ l1_pre_topc(X0_50)
% 8.19/1.47      | ~ v2_pre_topc(X1_50)
% 8.19/1.47      | ~ v2_pre_topc(X0_50)
% 8.19/1.47      | ~ v1_funct_1(X0_51) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_10]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_876,plain,
% 8.19/1.47      ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
% 8.19/1.47      | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 8.19/1.47      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 8.19/1.47      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 8.19/1.47      | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
% 8.19/1.47      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 8.19/1.47      | v2_struct_0(X1_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X0_50) = iProver_top
% 8.19/1.47      | v2_struct_0(X2_50) = iProver_top
% 8.19/1.47      | l1_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | l1_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X1_50) != iProver_top
% 8.19/1.47      | v2_pre_topc(X0_50) != iProver_top
% 8.19/1.47      | v1_funct_1(X0_51) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_12825,plain,
% 8.19/1.47      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
% 8.19/1.47      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 8.19/1.47      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 8.19/1.47      | m1_pre_topc(sK2,sK3) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 8.19/1.47      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 8.19/1.47      | v2_struct_0(sK3) = iProver_top
% 8.19/1.47      | v2_struct_0(sK1) = iProver_top
% 8.19/1.47      | v2_struct_0(sK2) = iProver_top
% 8.19/1.47      | l1_pre_topc(sK3) != iProver_top
% 8.19/1.47      | l1_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK3) != iProver_top
% 8.19/1.47      | v2_pre_topc(sK1) != iProver_top
% 8.19/1.47      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_12808,c_876]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_23942,plain,
% 8.19/1.47      ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
% 8.19/1.47      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 8.19/1.47      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top ),
% 8.19/1.47      inference(global_propositional_subsumption,
% 8.19/1.47                [status(thm)],
% 8.19/1.47                [c_12825,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_40,c_41,
% 8.19/1.47                 c_42,c_43,c_44,c_45,c_59,c_1249,c_1342,c_2765,c_2766,
% 8.19/1.47                 c_2767]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_23943,plain,
% 8.19/1.47      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
% 8.19/1.47      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,u1_struct_0(sK3)) != iProver_top
% 8.19/1.47      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 8.19/1.47      inference(renaming,[status(thm)],[c_23942]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_23949,plain,
% 8.19/1.47      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
% 8.19/1.47      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 8.19/1.47      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 8.19/1.47      inference(superposition,[status(thm)],[c_898,c_23943]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_17,negated_conjecture,
% 8.19/1.47      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 8.19/1.47      inference(cnf_transformation,[],[f69]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_332,negated_conjecture,
% 8.19/1.47      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 8.19/1.47      inference(subtyping,[status(esa)],[c_17]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_882,plain,
% 8.19/1.47      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_897,plain,
% 8.19/1.47      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 8.19/1.47      inference(light_normalisation,[status(thm)],[c_882,c_334]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_13,negated_conjecture,
% 8.19/1.47      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
% 8.19/1.47      inference(cnf_transformation,[],[f73]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_49,plain,
% 8.19/1.47      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_16,negated_conjecture,
% 8.19/1.47      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 8.19/1.47      inference(cnf_transformation,[],[f70]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(c_47,plain,
% 8.19/1.47      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 8.19/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.19/1.47  
% 8.19/1.47  cnf(contradiction,plain,
% 8.19/1.47      ( $false ),
% 8.19/1.47      inference(minisat,[status(thm)],[c_23949,c_897,c_49,c_47]) ).
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 8.19/1.47  
% 8.19/1.47  ------                               Statistics
% 8.19/1.47  
% 8.19/1.47  ------ General
% 8.19/1.47  
% 8.19/1.47  abstr_ref_over_cycles:                  0
% 8.19/1.47  abstr_ref_under_cycles:                 0
% 8.19/1.47  gc_basic_clause_elim:                   0
% 8.19/1.47  forced_gc_time:                         0
% 8.19/1.47  parsing_time:                           0.01
% 8.19/1.47  unif_index_cands_time:                  0.
% 8.19/1.47  unif_index_add_time:                    0.
% 8.19/1.47  orderings_time:                         0.
% 8.19/1.47  out_proof_time:                         0.02
% 8.19/1.47  total_time:                             0.998
% 8.19/1.47  num_of_symbols:                         54
% 8.19/1.47  num_of_terms:                           23703
% 8.19/1.47  
% 8.19/1.47  ------ Preprocessing
% 8.19/1.47  
% 8.19/1.47  num_of_splits:                          0
% 8.19/1.47  num_of_split_atoms:                     0
% 8.19/1.47  num_of_reused_defs:                     0
% 8.19/1.47  num_eq_ax_congr_red:                    34
% 8.19/1.47  num_of_sem_filtered_clauses:            1
% 8.19/1.47  num_of_subtypes:                        4
% 8.19/1.47  monotx_restored_types:                  0
% 8.19/1.47  sat_num_of_epr_types:                   0
% 8.19/1.47  sat_num_of_non_cyclic_types:            0
% 8.19/1.47  sat_guarded_non_collapsed_types:        1
% 8.19/1.47  num_pure_diseq_elim:                    0
% 8.19/1.47  simp_replaced_by:                       0
% 8.19/1.47  res_preprocessed:                       113
% 8.19/1.47  prep_upred:                             0
% 8.19/1.47  prep_unflattend:                        0
% 8.19/1.47  smt_new_axioms:                         0
% 8.19/1.47  pred_elim_cands:                        9
% 8.19/1.47  pred_elim:                              0
% 8.19/1.47  pred_elim_cl:                           0
% 8.19/1.47  pred_elim_cycles:                       1
% 8.19/1.47  merged_defs:                            0
% 8.19/1.47  merged_defs_ncl:                        0
% 8.19/1.47  bin_hyper_res:                          0
% 8.19/1.47  prep_cycles:                            3
% 8.19/1.47  pred_elim_time:                         0.
% 8.19/1.47  splitting_time:                         0.
% 8.19/1.47  sem_filter_time:                        0.
% 8.19/1.47  monotx_time:                            0.
% 8.19/1.47  subtype_inf_time:                       0.001
% 8.19/1.47  
% 8.19/1.47  ------ Problem properties
% 8.19/1.47  
% 8.19/1.47  clauses:                                32
% 8.19/1.47  conjectures:                            19
% 8.19/1.47  epr:                                    17
% 8.19/1.47  horn:                                   25
% 8.19/1.47  ground:                                 19
% 8.19/1.47  unary:                                  19
% 8.19/1.47  binary:                                 1
% 8.19/1.47  lits:                                   139
% 8.19/1.47  lits_eq:                                4
% 8.19/1.47  fd_pure:                                0
% 8.19/1.47  fd_pseudo:                              0
% 8.19/1.47  fd_cond:                                0
% 8.19/1.47  fd_pseudo_cond:                         1
% 8.19/1.47  ac_symbols:                             0
% 8.19/1.47  
% 8.19/1.47  ------ Propositional Solver
% 8.19/1.47  
% 8.19/1.47  prop_solver_calls:                      29
% 8.19/1.47  prop_fast_solver_calls:                 4593
% 8.19/1.47  smt_solver_calls:                       0
% 8.19/1.47  smt_fast_solver_calls:                  0
% 8.19/1.47  prop_num_of_clauses:                    7724
% 8.19/1.47  prop_preprocess_simplified:             19349
% 8.19/1.47  prop_fo_subsumed:                       1744
% 8.19/1.47  prop_solver_time:                       0.
% 8.19/1.47  smt_solver_time:                        0.
% 8.19/1.47  smt_fast_solver_time:                   0.
% 8.19/1.47  prop_fast_solver_time:                  0.
% 8.19/1.47  prop_unsat_core_time:                   0.001
% 8.19/1.47  
% 8.19/1.47  ------ QBF
% 8.19/1.47  
% 8.19/1.47  qbf_q_res:                              0
% 8.19/1.47  qbf_num_tautologies:                    0
% 8.19/1.47  qbf_prep_cycles:                        0
% 8.19/1.47  
% 8.19/1.47  ------ BMC1
% 8.19/1.47  
% 8.19/1.47  bmc1_current_bound:                     -1
% 8.19/1.47  bmc1_last_solved_bound:                 -1
% 8.19/1.47  bmc1_unsat_core_size:                   -1
% 8.19/1.47  bmc1_unsat_core_parents_size:           -1
% 8.19/1.47  bmc1_merge_next_fun:                    0
% 8.19/1.47  bmc1_unsat_core_clauses_time:           0.
% 8.19/1.47  
% 8.19/1.47  ------ Instantiation
% 8.19/1.47  
% 8.19/1.47  inst_num_of_clauses:                    2680
% 8.19/1.47  inst_num_in_passive:                    202
% 8.19/1.47  inst_num_in_active:                     1215
% 8.19/1.47  inst_num_in_unprocessed:                1264
% 8.19/1.47  inst_num_of_loops:                      1350
% 8.19/1.47  inst_num_of_learning_restarts:          0
% 8.19/1.47  inst_num_moves_active_passive:          129
% 8.19/1.47  inst_lit_activity:                      0
% 8.19/1.47  inst_lit_activity_moves:                0
% 8.19/1.47  inst_num_tautologies:                   0
% 8.19/1.47  inst_num_prop_implied:                  0
% 8.19/1.47  inst_num_existing_simplified:           0
% 8.19/1.47  inst_num_eq_res_simplified:             0
% 8.19/1.47  inst_num_child_elim:                    0
% 8.19/1.47  inst_num_of_dismatching_blockings:      3917
% 8.19/1.47  inst_num_of_non_proper_insts:           4575
% 8.19/1.47  inst_num_of_duplicates:                 0
% 8.19/1.47  inst_inst_num_from_inst_to_res:         0
% 8.19/1.47  inst_dismatching_checking_time:         0.
% 8.19/1.47  
% 8.19/1.47  ------ Resolution
% 8.19/1.47  
% 8.19/1.47  res_num_of_clauses:                     0
% 8.19/1.47  res_num_in_passive:                     0
% 8.19/1.47  res_num_in_active:                      0
% 8.19/1.47  res_num_of_loops:                       116
% 8.19/1.47  res_forward_subset_subsumed:            253
% 8.19/1.47  res_backward_subset_subsumed:           2
% 8.19/1.47  res_forward_subsumed:                   0
% 8.19/1.47  res_backward_subsumed:                  0
% 8.19/1.47  res_forward_subsumption_resolution:     0
% 8.19/1.47  res_backward_subsumption_resolution:    0
% 8.19/1.47  res_clause_to_clause_subsumption:       882
% 8.19/1.47  res_orphan_elimination:                 0
% 8.19/1.47  res_tautology_del:                      364
% 8.19/1.47  res_num_eq_res_simplified:              0
% 8.19/1.47  res_num_sel_changes:                    0
% 8.19/1.47  res_moves_from_active_to_pass:          0
% 8.19/1.47  
% 8.19/1.47  ------ Superposition
% 8.19/1.47  
% 8.19/1.47  sup_time_total:                         0.
% 8.19/1.47  sup_time_generating:                    0.
% 8.19/1.47  sup_time_sim_full:                      0.
% 8.19/1.47  sup_time_sim_immed:                     0.
% 8.19/1.47  
% 8.19/1.47  sup_num_of_clauses:                     247
% 8.19/1.47  sup_num_in_active:                      160
% 8.19/1.47  sup_num_in_passive:                     87
% 8.19/1.47  sup_num_of_loops:                       268
% 8.19/1.47  sup_fw_superposition:                   180
% 8.19/1.47  sup_bw_superposition:                   328
% 8.19/1.47  sup_immediate_simplified:               144
% 8.19/1.47  sup_given_eliminated:                   2
% 8.19/1.47  comparisons_done:                       0
% 8.19/1.47  comparisons_avoided:                    0
% 8.19/1.47  
% 8.19/1.47  ------ Simplifications
% 8.19/1.47  
% 8.19/1.47  
% 8.19/1.47  sim_fw_subset_subsumed:                 31
% 8.19/1.47  sim_bw_subset_subsumed:                 24
% 8.19/1.47  sim_fw_subsumed:                        26
% 8.19/1.47  sim_bw_subsumed:                        2
% 8.19/1.47  sim_fw_subsumption_res:                 0
% 8.19/1.47  sim_bw_subsumption_res:                 0
% 8.19/1.47  sim_tautology_del:                      13
% 8.19/1.47  sim_eq_tautology_del:                   7
% 8.19/1.47  sim_eq_res_simp:                        0
% 8.19/1.47  sim_fw_demodulated:                     29
% 8.19/1.47  sim_bw_demodulated:                     107
% 8.19/1.47  sim_light_normalised:                   122
% 8.19/1.47  sim_joinable_taut:                      0
% 8.19/1.47  sim_joinable_simp:                      0
% 8.19/1.47  sim_ac_normalised:                      0
% 8.19/1.47  sim_smt_subsumption:                    0
% 8.19/1.47  
%------------------------------------------------------------------------------
