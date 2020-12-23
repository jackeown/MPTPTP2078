%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:06 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  250 (26749 expanded)
%              Number of clauses        :  174 (5435 expanded)
%              Number of leaves         :   23 (12723 expanded)
%              Depth                    :   37
%              Number of atoms          : 1602 (413444 expanded)
%              Number of equality atoms :  599 (38807 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f43,f42,f41,f40,f39,f38,f37])).

fof(f76,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
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
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_416,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_997,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_16,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_415,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1053,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_997,c_415])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_408,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1004,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_412,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1000,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_10,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_421,plain,
    ( m1_pre_topc(X0_50,X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_992,plain,
    ( m1_pre_topc(X0_50,X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_411,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1001,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_425,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_988,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_418,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X0_50)
    | m1_pre_topc(X2_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_995,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X2_50,X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1225,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_988,c_995])).

cnf(c_3220,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_1225])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3495,plain,
    ( l1_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3220,c_36,c_37,c_38,c_43,c_44])).

cnf(c_3496,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3495])).

cnf(c_3507,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_992,c_3496])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_34,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3609,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(sK0,sK1,sK0,X0_50,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3507,c_33,c_34,c_35])).

cnf(c_3610,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)
    | m1_pre_topc(X0_50,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3609])).

cnf(c_3617,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1004,c_3610])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_426,plain,
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
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_987,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_2412,plain,
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
    inference(superposition,[status(thm)],[c_1001,c_987])).

cnf(c_2991,plain,
    ( m1_pre_topc(X0_50,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_33,c_34,c_35,c_36,c_37,c_38,c_43,c_44])).

cnf(c_2992,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
    | m1_pre_topc(X0_50,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2991])).

cnf(c_2999,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1004,c_2992])).

cnf(c_3629,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3617,c_2999])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_424,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_989,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_3731,plain,
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
    inference(superposition,[status(thm)],[c_3629,c_989])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_58,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_60,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_4799,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3731,c_33,c_34,c_35,c_36,c_37,c_38,c_42,c_43,c_44,c_45,c_60])).

cnf(c_4804,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4799,c_1225])).

cnf(c_59,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_433,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_450,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_439,plain,
    ( X0_51 != X1_51
    | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = k2_tmap_1(X0_50,X1_50,X1_51,X2_50) ),
    theory(equality)).

cnf(c_2144,plain,
    ( X0_51 != sK4
    | k2_tmap_1(sK0,sK1,X0_51,sK3) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_2147,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_1417,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_2149,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_438,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(X1_51)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_2525,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != X0_51 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_3058,plain,
    ( ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4))
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k3_tmap_1(X0_50,sK1,sK0,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_3060,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k3_tmap_1(X0_50,sK1,sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3058])).

cnf(c_3062,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3060])).

cnf(c_1432,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X0_50,sK0)
    | ~ m1_pre_topc(sK0,X1_50)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_3059,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,X0_50)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_50,sK1,sK0,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_3065,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3059])).

cnf(c_434,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2346,plain,
    ( X0_51 != X1_51
    | k2_tmap_1(sK0,sK1,sK4,sK3) != X1_51
    | k2_tmap_1(sK0,sK1,sK4,sK3) = X0_51 ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_2812,plain,
    ( X0_51 != k2_tmap_1(sK0,sK1,X1_51,sK3)
    | k2_tmap_1(sK0,sK1,sK4,sK3) = X0_51
    | k2_tmap_1(sK0,sK1,sK4,sK3) != k2_tmap_1(sK0,sK1,X1_51,sK3) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_3304,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k2_tmap_1(sK0,sK1,sK4,sK3)
    | k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | k2_tmap_1(sK0,sK1,sK4,sK3) != k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2812])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1412,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(sK0,X1_50)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_3455,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_50)
    | ~ m1_pre_topc(sK0,X0_50)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_3456,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | m1_pre_topc(sK0,X0_50) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3455])).

cnf(c_3458,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_2332,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | k2_tmap_1(sK0,sK1,sK4,sK3) != X0_51 ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_3513,plain,
    ( ~ v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)))
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | k2_tmap_1(sK0,sK1,sK4,sK3) != k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_3514,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) != k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3513])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_990,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_3732,plain,
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
    inference(superposition,[status(thm)],[c_3629,c_990])).

cnf(c_5816,plain,
    ( l1_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4804,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,c_37,c_27,c_38,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3732])).

cnf(c_5817,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(X0_50,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5816])).

cnf(c_5828,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_5817])).

cnf(c_4806,plain,
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
    inference(superposition,[status(thm)],[c_4799,c_987])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_428,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_985,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_2023,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_985])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_429,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_984,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_2064,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_984])).

cnf(c_5655,plain,
    ( m1_pre_topc(X0_50,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4806,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,c_37,c_27,c_38,c_41,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,c_59,c_60,c_450,c_2023,c_2064,c_2147,c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3732])).

cnf(c_5656,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
    | m1_pre_topc(X0_50,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5655])).

cnf(c_5663,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_1000,c_5656])).

cnf(c_5847,plain,
    ( k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | m1_pre_topc(sK3,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5828,c_5663])).

cnf(c_6018,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1004,c_5847])).

cnf(c_5857,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5847])).

cnf(c_6317,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6018,c_33,c_34,c_35,c_42,c_5857])).

cnf(c_12,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_419,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_994,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1283,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_994,c_995])).

cnf(c_6320,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6317,c_1283])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_46,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6855,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6320,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_41,c_42,c_43,c_44,c_45,c_46])).

cnf(c_6321,plain,
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
    inference(superposition,[status(thm)],[c_6317,c_989])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_40,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6747,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6321,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,c_37,c_27,c_38,c_40,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3731,c_3732])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_430,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
    | ~ v1_funct_2(X1_51,X0_52,X1_52)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | X0_51 = X1_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_983,plain,
    ( X0_51 = X1_51
    | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_6755,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6747,c_983])).

cnf(c_6323,plain,
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
    inference(superposition,[status(thm)],[c_6317,c_990])).

cnf(c_991,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_4805,plain,
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
    inference(superposition,[status(thm)],[c_4799,c_991])).

cnf(c_5537,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4805,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,c_37,c_27,c_38,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3732])).

cnf(c_5538,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK3,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5537])).

cnf(c_6324,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6317,c_5538])).

cnf(c_7125,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6755,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,c_37,c_27,c_38,c_40,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3731,c_3732,c_6323,c_6324])).

cnf(c_7126,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_7125])).

cnf(c_7136,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6855,c_7126])).

cnf(c_406,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1006,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_3618,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_1006,c_3610])).

cnf(c_3000,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_1006,c_2992])).

cnf(c_3626,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3618,c_3000])).

cnf(c_3664,plain,
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
    inference(superposition,[status(thm)],[c_3626,c_989])).

cnf(c_3665,plain,
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
    inference(superposition,[status(thm)],[c_3626,c_990])).

cnf(c_2507,plain,
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
    inference(superposition,[status(thm)],[c_1001,c_991])).

cnf(c_3195,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_36,c_37,c_38,c_43,c_44])).

cnf(c_3196,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK0,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3195])).

cnf(c_3666,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3626,c_3196])).

cnf(c_7148,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7136,c_33,c_34,c_35,c_36,c_37,c_38,c_40,c_43,c_44,c_45,c_60,c_3664,c_3665,c_3666])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_420,plain,
    ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
    | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51)
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_993,plain,
    ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
    | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_427,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | m1_subset_1(X0_51,u1_struct_0(X1_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_986,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1253,plain,
    ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
    | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_993,c_986])).

cnf(c_7181,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
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
    inference(superposition,[status(thm)],[c_7148,c_1253])).

cnf(c_25924,plain,
    ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7181,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,c_37,c_27,c_38,c_39,c_41,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,c_46,c_59,c_60,c_450,c_2023,c_2064,c_2147,c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3731,c_3732])).

cnf(c_25925,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_25924])).

cnf(c_25934,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_25925])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_50,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_48,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25934,c_50,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:45:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.60/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.60/1.48  
% 7.60/1.48  ------  iProver source info
% 7.60/1.48  
% 7.60/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.60/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.60/1.48  git: non_committed_changes: false
% 7.60/1.48  git: last_make_outside_of_git: false
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  
% 7.60/1.48  ------ Input Options
% 7.60/1.48  
% 7.60/1.48  --out_options                           all
% 7.60/1.48  --tptp_safe_out                         true
% 7.60/1.48  --problem_path                          ""
% 7.60/1.48  --include_path                          ""
% 7.60/1.48  --clausifier                            res/vclausify_rel
% 7.60/1.48  --clausifier_options                    --mode clausify
% 7.60/1.48  --stdin                                 false
% 7.60/1.48  --stats_out                             all
% 7.60/1.48  
% 7.60/1.48  ------ General Options
% 7.60/1.48  
% 7.60/1.48  --fof                                   false
% 7.60/1.48  --time_out_real                         305.
% 7.60/1.48  --time_out_virtual                      -1.
% 7.60/1.48  --symbol_type_check                     false
% 7.60/1.48  --clausify_out                          false
% 7.60/1.48  --sig_cnt_out                           false
% 7.60/1.48  --trig_cnt_out                          false
% 7.60/1.48  --trig_cnt_out_tolerance                1.
% 7.60/1.48  --trig_cnt_out_sk_spl                   false
% 7.60/1.48  --abstr_cl_out                          false
% 7.60/1.48  
% 7.60/1.48  ------ Global Options
% 7.60/1.48  
% 7.60/1.48  --schedule                              default
% 7.60/1.48  --add_important_lit                     false
% 7.60/1.48  --prop_solver_per_cl                    1000
% 7.60/1.48  --min_unsat_core                        false
% 7.60/1.48  --soft_assumptions                      false
% 7.60/1.48  --soft_lemma_size                       3
% 7.60/1.48  --prop_impl_unit_size                   0
% 7.60/1.48  --prop_impl_unit                        []
% 7.60/1.48  --share_sel_clauses                     true
% 7.60/1.48  --reset_solvers                         false
% 7.60/1.48  --bc_imp_inh                            [conj_cone]
% 7.60/1.48  --conj_cone_tolerance                   3.
% 7.60/1.48  --extra_neg_conj                        none
% 7.60/1.48  --large_theory_mode                     true
% 7.60/1.48  --prolific_symb_bound                   200
% 7.60/1.48  --lt_threshold                          2000
% 7.60/1.48  --clause_weak_htbl                      true
% 7.60/1.48  --gc_record_bc_elim                     false
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing Options
% 7.60/1.48  
% 7.60/1.48  --preprocessing_flag                    true
% 7.60/1.48  --time_out_prep_mult                    0.1
% 7.60/1.48  --splitting_mode                        input
% 7.60/1.48  --splitting_grd                         true
% 7.60/1.48  --splitting_cvd                         false
% 7.60/1.48  --splitting_cvd_svl                     false
% 7.60/1.48  --splitting_nvd                         32
% 7.60/1.48  --sub_typing                            true
% 7.60/1.48  --prep_gs_sim                           true
% 7.60/1.48  --prep_unflatten                        true
% 7.60/1.48  --prep_res_sim                          true
% 7.60/1.48  --prep_upred                            true
% 7.60/1.48  --prep_sem_filter                       exhaustive
% 7.60/1.48  --prep_sem_filter_out                   false
% 7.60/1.48  --pred_elim                             true
% 7.60/1.48  --res_sim_input                         true
% 7.60/1.48  --eq_ax_congr_red                       true
% 7.60/1.48  --pure_diseq_elim                       true
% 7.60/1.48  --brand_transform                       false
% 7.60/1.48  --non_eq_to_eq                          false
% 7.60/1.48  --prep_def_merge                        true
% 7.60/1.48  --prep_def_merge_prop_impl              false
% 7.60/1.48  --prep_def_merge_mbd                    true
% 7.60/1.48  --prep_def_merge_tr_red                 false
% 7.60/1.48  --prep_def_merge_tr_cl                  false
% 7.60/1.48  --smt_preprocessing                     true
% 7.60/1.48  --smt_ac_axioms                         fast
% 7.60/1.48  --preprocessed_out                      false
% 7.60/1.48  --preprocessed_stats                    false
% 7.60/1.48  
% 7.60/1.48  ------ Abstraction refinement Options
% 7.60/1.48  
% 7.60/1.48  --abstr_ref                             []
% 7.60/1.48  --abstr_ref_prep                        false
% 7.60/1.48  --abstr_ref_until_sat                   false
% 7.60/1.48  --abstr_ref_sig_restrict                funpre
% 7.60/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.60/1.48  --abstr_ref_under                       []
% 7.60/1.48  
% 7.60/1.48  ------ SAT Options
% 7.60/1.48  
% 7.60/1.48  --sat_mode                              false
% 7.60/1.48  --sat_fm_restart_options                ""
% 7.60/1.48  --sat_gr_def                            false
% 7.60/1.48  --sat_epr_types                         true
% 7.60/1.48  --sat_non_cyclic_types                  false
% 7.60/1.48  --sat_finite_models                     false
% 7.60/1.48  --sat_fm_lemmas                         false
% 7.60/1.48  --sat_fm_prep                           false
% 7.60/1.48  --sat_fm_uc_incr                        true
% 7.60/1.48  --sat_out_model                         small
% 7.60/1.48  --sat_out_clauses                       false
% 7.60/1.48  
% 7.60/1.48  ------ QBF Options
% 7.60/1.48  
% 7.60/1.48  --qbf_mode                              false
% 7.60/1.48  --qbf_elim_univ                         false
% 7.60/1.48  --qbf_dom_inst                          none
% 7.60/1.48  --qbf_dom_pre_inst                      false
% 7.60/1.48  --qbf_sk_in                             false
% 7.60/1.48  --qbf_pred_elim                         true
% 7.60/1.48  --qbf_split                             512
% 7.60/1.48  
% 7.60/1.48  ------ BMC1 Options
% 7.60/1.48  
% 7.60/1.48  --bmc1_incremental                      false
% 7.60/1.48  --bmc1_axioms                           reachable_all
% 7.60/1.48  --bmc1_min_bound                        0
% 7.60/1.48  --bmc1_max_bound                        -1
% 7.60/1.48  --bmc1_max_bound_default                -1
% 7.60/1.48  --bmc1_symbol_reachability              true
% 7.60/1.48  --bmc1_property_lemmas                  false
% 7.60/1.48  --bmc1_k_induction                      false
% 7.60/1.48  --bmc1_non_equiv_states                 false
% 7.60/1.48  --bmc1_deadlock                         false
% 7.60/1.48  --bmc1_ucm                              false
% 7.60/1.48  --bmc1_add_unsat_core                   none
% 7.60/1.48  --bmc1_unsat_core_children              false
% 7.60/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.60/1.48  --bmc1_out_stat                         full
% 7.60/1.48  --bmc1_ground_init                      false
% 7.60/1.48  --bmc1_pre_inst_next_state              false
% 7.60/1.48  --bmc1_pre_inst_state                   false
% 7.60/1.48  --bmc1_pre_inst_reach_state             false
% 7.60/1.48  --bmc1_out_unsat_core                   false
% 7.60/1.48  --bmc1_aig_witness_out                  false
% 7.60/1.48  --bmc1_verbose                          false
% 7.60/1.48  --bmc1_dump_clauses_tptp                false
% 7.60/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.60/1.48  --bmc1_dump_file                        -
% 7.60/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.60/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.60/1.48  --bmc1_ucm_extend_mode                  1
% 7.60/1.48  --bmc1_ucm_init_mode                    2
% 7.60/1.48  --bmc1_ucm_cone_mode                    none
% 7.60/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.60/1.48  --bmc1_ucm_relax_model                  4
% 7.60/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.60/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.60/1.48  --bmc1_ucm_layered_model                none
% 7.60/1.48  --bmc1_ucm_max_lemma_size               10
% 7.60/1.48  
% 7.60/1.48  ------ AIG Options
% 7.60/1.48  
% 7.60/1.48  --aig_mode                              false
% 7.60/1.48  
% 7.60/1.48  ------ Instantiation Options
% 7.60/1.48  
% 7.60/1.48  --instantiation_flag                    true
% 7.60/1.48  --inst_sos_flag                         false
% 7.60/1.48  --inst_sos_phase                        true
% 7.60/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel_side                     num_symb
% 7.60/1.48  --inst_solver_per_active                1400
% 7.60/1.48  --inst_solver_calls_frac                1.
% 7.60/1.48  --inst_passive_queue_type               priority_queues
% 7.60/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.60/1.48  --inst_passive_queues_freq              [25;2]
% 7.60/1.48  --inst_dismatching                      true
% 7.60/1.48  --inst_eager_unprocessed_to_passive     true
% 7.60/1.48  --inst_prop_sim_given                   true
% 7.60/1.48  --inst_prop_sim_new                     false
% 7.60/1.48  --inst_subs_new                         false
% 7.60/1.48  --inst_eq_res_simp                      false
% 7.60/1.48  --inst_subs_given                       false
% 7.60/1.48  --inst_orphan_elimination               true
% 7.60/1.48  --inst_learning_loop_flag               true
% 7.60/1.48  --inst_learning_start                   3000
% 7.60/1.48  --inst_learning_factor                  2
% 7.60/1.48  --inst_start_prop_sim_after_learn       3
% 7.60/1.48  --inst_sel_renew                        solver
% 7.60/1.48  --inst_lit_activity_flag                true
% 7.60/1.48  --inst_restr_to_given                   false
% 7.60/1.48  --inst_activity_threshold               500
% 7.60/1.48  --inst_out_proof                        true
% 7.60/1.48  
% 7.60/1.48  ------ Resolution Options
% 7.60/1.48  
% 7.60/1.48  --resolution_flag                       true
% 7.60/1.48  --res_lit_sel                           adaptive
% 7.60/1.48  --res_lit_sel_side                      none
% 7.60/1.48  --res_ordering                          kbo
% 7.60/1.48  --res_to_prop_solver                    active
% 7.60/1.48  --res_prop_simpl_new                    false
% 7.60/1.48  --res_prop_simpl_given                  true
% 7.60/1.48  --res_passive_queue_type                priority_queues
% 7.60/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.60/1.48  --res_passive_queues_freq               [15;5]
% 7.60/1.48  --res_forward_subs                      full
% 7.60/1.48  --res_backward_subs                     full
% 7.60/1.48  --res_forward_subs_resolution           true
% 7.60/1.48  --res_backward_subs_resolution          true
% 7.60/1.48  --res_orphan_elimination                true
% 7.60/1.48  --res_time_limit                        2.
% 7.60/1.48  --res_out_proof                         true
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Options
% 7.60/1.48  
% 7.60/1.48  --superposition_flag                    true
% 7.60/1.48  --sup_passive_queue_type                priority_queues
% 7.60/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.60/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.60/1.48  --demod_completeness_check              fast
% 7.60/1.48  --demod_use_ground                      true
% 7.60/1.48  --sup_to_prop_solver                    passive
% 7.60/1.48  --sup_prop_simpl_new                    true
% 7.60/1.48  --sup_prop_simpl_given                  true
% 7.60/1.48  --sup_fun_splitting                     false
% 7.60/1.48  --sup_smt_interval                      50000
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Simplification Setup
% 7.60/1.48  
% 7.60/1.48  --sup_indices_passive                   []
% 7.60/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.60/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.60/1.48  --sup_full_bw                           [BwDemod]
% 7.60/1.48  --sup_immed_triv                        [TrivRules]
% 7.60/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.60/1.48  --sup_immed_bw_main                     []
% 7.60/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.60/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.60/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.60/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.60/1.48  
% 7.60/1.48  ------ Combination Options
% 7.60/1.48  
% 7.60/1.48  --comb_res_mult                         3
% 7.60/1.48  --comb_sup_mult                         2
% 7.60/1.48  --comb_inst_mult                        10
% 7.60/1.48  
% 7.60/1.48  ------ Debug Options
% 7.60/1.48  
% 7.60/1.48  --dbg_backtrace                         false
% 7.60/1.48  --dbg_dump_prop_clauses                 false
% 7.60/1.48  --dbg_dump_prop_clauses_file            -
% 7.60/1.48  --dbg_out_stat                          false
% 7.60/1.48  ------ Parsing...
% 7.60/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  ------ Proving...
% 7.60/1.48  ------ Problem Properties 
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  clauses                                 33
% 7.60/1.48  conjectures                             19
% 7.60/1.48  EPR                                     17
% 7.60/1.48  Horn                                    25
% 7.60/1.48  unary                                   19
% 7.60/1.48  binary                                  1
% 7.60/1.48  lits                                    141
% 7.60/1.48  lits eq                                 4
% 7.60/1.48  fd_pure                                 0
% 7.60/1.48  fd_pseudo                               0
% 7.60/1.48  fd_cond                                 0
% 7.60/1.48  fd_pseudo_cond                          1
% 7.60/1.48  AC symbols                              0
% 7.60/1.48  
% 7.60/1.48  ------ Schedule dynamic 5 is on 
% 7.60/1.48  
% 7.60/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  Current options:
% 7.60/1.48  ------ 
% 7.60/1.48  
% 7.60/1.48  ------ Input Options
% 7.60/1.48  
% 7.60/1.48  --out_options                           all
% 7.60/1.48  --tptp_safe_out                         true
% 7.60/1.48  --problem_path                          ""
% 7.60/1.48  --include_path                          ""
% 7.60/1.48  --clausifier                            res/vclausify_rel
% 7.60/1.48  --clausifier_options                    --mode clausify
% 7.60/1.48  --stdin                                 false
% 7.60/1.48  --stats_out                             all
% 7.60/1.48  
% 7.60/1.48  ------ General Options
% 7.60/1.48  
% 7.60/1.48  --fof                                   false
% 7.60/1.48  --time_out_real                         305.
% 7.60/1.48  --time_out_virtual                      -1.
% 7.60/1.48  --symbol_type_check                     false
% 7.60/1.48  --clausify_out                          false
% 7.60/1.48  --sig_cnt_out                           false
% 7.60/1.48  --trig_cnt_out                          false
% 7.60/1.48  --trig_cnt_out_tolerance                1.
% 7.60/1.48  --trig_cnt_out_sk_spl                   false
% 7.60/1.48  --abstr_cl_out                          false
% 7.60/1.48  
% 7.60/1.48  ------ Global Options
% 7.60/1.48  
% 7.60/1.48  --schedule                              default
% 7.60/1.48  --add_important_lit                     false
% 7.60/1.48  --prop_solver_per_cl                    1000
% 7.60/1.48  --min_unsat_core                        false
% 7.60/1.48  --soft_assumptions                      false
% 7.60/1.48  --soft_lemma_size                       3
% 7.60/1.48  --prop_impl_unit_size                   0
% 7.60/1.48  --prop_impl_unit                        []
% 7.60/1.48  --share_sel_clauses                     true
% 7.60/1.48  --reset_solvers                         false
% 7.60/1.48  --bc_imp_inh                            [conj_cone]
% 7.60/1.48  --conj_cone_tolerance                   3.
% 7.60/1.48  --extra_neg_conj                        none
% 7.60/1.48  --large_theory_mode                     true
% 7.60/1.48  --prolific_symb_bound                   200
% 7.60/1.48  --lt_threshold                          2000
% 7.60/1.48  --clause_weak_htbl                      true
% 7.60/1.48  --gc_record_bc_elim                     false
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing Options
% 7.60/1.48  
% 7.60/1.48  --preprocessing_flag                    true
% 7.60/1.48  --time_out_prep_mult                    0.1
% 7.60/1.48  --splitting_mode                        input
% 7.60/1.48  --splitting_grd                         true
% 7.60/1.48  --splitting_cvd                         false
% 7.60/1.48  --splitting_cvd_svl                     false
% 7.60/1.48  --splitting_nvd                         32
% 7.60/1.48  --sub_typing                            true
% 7.60/1.48  --prep_gs_sim                           true
% 7.60/1.48  --prep_unflatten                        true
% 7.60/1.48  --prep_res_sim                          true
% 7.60/1.48  --prep_upred                            true
% 7.60/1.48  --prep_sem_filter                       exhaustive
% 7.60/1.48  --prep_sem_filter_out                   false
% 7.60/1.48  --pred_elim                             true
% 7.60/1.48  --res_sim_input                         true
% 7.60/1.48  --eq_ax_congr_red                       true
% 7.60/1.48  --pure_diseq_elim                       true
% 7.60/1.48  --brand_transform                       false
% 7.60/1.48  --non_eq_to_eq                          false
% 7.60/1.48  --prep_def_merge                        true
% 7.60/1.48  --prep_def_merge_prop_impl              false
% 7.60/1.48  --prep_def_merge_mbd                    true
% 7.60/1.48  --prep_def_merge_tr_red                 false
% 7.60/1.48  --prep_def_merge_tr_cl                  false
% 7.60/1.48  --smt_preprocessing                     true
% 7.60/1.48  --smt_ac_axioms                         fast
% 7.60/1.48  --preprocessed_out                      false
% 7.60/1.48  --preprocessed_stats                    false
% 7.60/1.48  
% 7.60/1.48  ------ Abstraction refinement Options
% 7.60/1.48  
% 7.60/1.48  --abstr_ref                             []
% 7.60/1.48  --abstr_ref_prep                        false
% 7.60/1.48  --abstr_ref_until_sat                   false
% 7.60/1.48  --abstr_ref_sig_restrict                funpre
% 7.60/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.60/1.48  --abstr_ref_under                       []
% 7.60/1.48  
% 7.60/1.48  ------ SAT Options
% 7.60/1.48  
% 7.60/1.48  --sat_mode                              false
% 7.60/1.48  --sat_fm_restart_options                ""
% 7.60/1.48  --sat_gr_def                            false
% 7.60/1.48  --sat_epr_types                         true
% 7.60/1.48  --sat_non_cyclic_types                  false
% 7.60/1.48  --sat_finite_models                     false
% 7.60/1.48  --sat_fm_lemmas                         false
% 7.60/1.48  --sat_fm_prep                           false
% 7.60/1.48  --sat_fm_uc_incr                        true
% 7.60/1.48  --sat_out_model                         small
% 7.60/1.48  --sat_out_clauses                       false
% 7.60/1.48  
% 7.60/1.48  ------ QBF Options
% 7.60/1.48  
% 7.60/1.48  --qbf_mode                              false
% 7.60/1.48  --qbf_elim_univ                         false
% 7.60/1.48  --qbf_dom_inst                          none
% 7.60/1.48  --qbf_dom_pre_inst                      false
% 7.60/1.48  --qbf_sk_in                             false
% 7.60/1.48  --qbf_pred_elim                         true
% 7.60/1.48  --qbf_split                             512
% 7.60/1.48  
% 7.60/1.48  ------ BMC1 Options
% 7.60/1.48  
% 7.60/1.48  --bmc1_incremental                      false
% 7.60/1.48  --bmc1_axioms                           reachable_all
% 7.60/1.48  --bmc1_min_bound                        0
% 7.60/1.48  --bmc1_max_bound                        -1
% 7.60/1.48  --bmc1_max_bound_default                -1
% 7.60/1.48  --bmc1_symbol_reachability              true
% 7.60/1.48  --bmc1_property_lemmas                  false
% 7.60/1.48  --bmc1_k_induction                      false
% 7.60/1.48  --bmc1_non_equiv_states                 false
% 7.60/1.48  --bmc1_deadlock                         false
% 7.60/1.48  --bmc1_ucm                              false
% 7.60/1.48  --bmc1_add_unsat_core                   none
% 7.60/1.48  --bmc1_unsat_core_children              false
% 7.60/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.60/1.48  --bmc1_out_stat                         full
% 7.60/1.48  --bmc1_ground_init                      false
% 7.60/1.48  --bmc1_pre_inst_next_state              false
% 7.60/1.48  --bmc1_pre_inst_state                   false
% 7.60/1.48  --bmc1_pre_inst_reach_state             false
% 7.60/1.48  --bmc1_out_unsat_core                   false
% 7.60/1.48  --bmc1_aig_witness_out                  false
% 7.60/1.48  --bmc1_verbose                          false
% 7.60/1.48  --bmc1_dump_clauses_tptp                false
% 7.60/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.60/1.48  --bmc1_dump_file                        -
% 7.60/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.60/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.60/1.48  --bmc1_ucm_extend_mode                  1
% 7.60/1.48  --bmc1_ucm_init_mode                    2
% 7.60/1.48  --bmc1_ucm_cone_mode                    none
% 7.60/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.60/1.48  --bmc1_ucm_relax_model                  4
% 7.60/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.60/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.60/1.48  --bmc1_ucm_layered_model                none
% 7.60/1.48  --bmc1_ucm_max_lemma_size               10
% 7.60/1.48  
% 7.60/1.48  ------ AIG Options
% 7.60/1.48  
% 7.60/1.48  --aig_mode                              false
% 7.60/1.48  
% 7.60/1.48  ------ Instantiation Options
% 7.60/1.48  
% 7.60/1.48  --instantiation_flag                    true
% 7.60/1.48  --inst_sos_flag                         false
% 7.60/1.48  --inst_sos_phase                        true
% 7.60/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel_side                     none
% 7.60/1.48  --inst_solver_per_active                1400
% 7.60/1.48  --inst_solver_calls_frac                1.
% 7.60/1.48  --inst_passive_queue_type               priority_queues
% 7.60/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.60/1.48  --inst_passive_queues_freq              [25;2]
% 7.60/1.48  --inst_dismatching                      true
% 7.60/1.48  --inst_eager_unprocessed_to_passive     true
% 7.60/1.48  --inst_prop_sim_given                   true
% 7.60/1.48  --inst_prop_sim_new                     false
% 7.60/1.48  --inst_subs_new                         false
% 7.60/1.48  --inst_eq_res_simp                      false
% 7.60/1.48  --inst_subs_given                       false
% 7.60/1.48  --inst_orphan_elimination               true
% 7.60/1.48  --inst_learning_loop_flag               true
% 7.60/1.48  --inst_learning_start                   3000
% 7.60/1.48  --inst_learning_factor                  2
% 7.60/1.48  --inst_start_prop_sim_after_learn       3
% 7.60/1.48  --inst_sel_renew                        solver
% 7.60/1.48  --inst_lit_activity_flag                true
% 7.60/1.48  --inst_restr_to_given                   false
% 7.60/1.48  --inst_activity_threshold               500
% 7.60/1.48  --inst_out_proof                        true
% 7.60/1.48  
% 7.60/1.48  ------ Resolution Options
% 7.60/1.48  
% 7.60/1.48  --resolution_flag                       false
% 7.60/1.48  --res_lit_sel                           adaptive
% 7.60/1.48  --res_lit_sel_side                      none
% 7.60/1.48  --res_ordering                          kbo
% 7.60/1.48  --res_to_prop_solver                    active
% 7.60/1.48  --res_prop_simpl_new                    false
% 7.60/1.48  --res_prop_simpl_given                  true
% 7.60/1.48  --res_passive_queue_type                priority_queues
% 7.60/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.60/1.48  --res_passive_queues_freq               [15;5]
% 7.60/1.48  --res_forward_subs                      full
% 7.60/1.48  --res_backward_subs                     full
% 7.60/1.48  --res_forward_subs_resolution           true
% 7.60/1.48  --res_backward_subs_resolution          true
% 7.60/1.48  --res_orphan_elimination                true
% 7.60/1.48  --res_time_limit                        2.
% 7.60/1.48  --res_out_proof                         true
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Options
% 7.60/1.48  
% 7.60/1.48  --superposition_flag                    true
% 7.60/1.48  --sup_passive_queue_type                priority_queues
% 7.60/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.60/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.60/1.48  --demod_completeness_check              fast
% 7.60/1.48  --demod_use_ground                      true
% 7.60/1.48  --sup_to_prop_solver                    passive
% 7.60/1.48  --sup_prop_simpl_new                    true
% 7.60/1.48  --sup_prop_simpl_given                  true
% 7.60/1.48  --sup_fun_splitting                     false
% 7.60/1.48  --sup_smt_interval                      50000
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Simplification Setup
% 7.60/1.48  
% 7.60/1.48  --sup_indices_passive                   []
% 7.60/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.60/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.60/1.48  --sup_full_bw                           [BwDemod]
% 7.60/1.48  --sup_immed_triv                        [TrivRules]
% 7.60/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.60/1.48  --sup_immed_bw_main                     []
% 7.60/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.60/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.60/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.60/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.60/1.48  
% 7.60/1.48  ------ Combination Options
% 7.60/1.48  
% 7.60/1.48  --comb_res_mult                         3
% 7.60/1.48  --comb_sup_mult                         2
% 7.60/1.48  --comb_inst_mult                        10
% 7.60/1.48  
% 7.60/1.48  ------ Debug Options
% 7.60/1.48  
% 7.60/1.48  --dbg_backtrace                         false
% 7.60/1.48  --dbg_dump_prop_clauses                 false
% 7.60/1.48  --dbg_dump_prop_clauses_file            -
% 7.60/1.48  --dbg_out_stat                          false
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS status Theorem for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  fof(f12,conjecture,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f13,negated_conjecture,(
% 7.60/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 7.60/1.48    inference(negated_conjecture,[],[f12])).
% 7.60/1.48  
% 7.60/1.48  fof(f34,plain,(
% 7.60/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f13])).
% 7.60/1.48  
% 7.60/1.48  fof(f35,plain,(
% 7.60/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f34])).
% 7.60/1.48  
% 7.60/1.48  fof(f43,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f42,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f41,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f40,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f39,plain,(
% 7.60/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f38,plain,(
% 7.60/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f37,plain,(
% 7.60/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f44,plain,(
% 7.60/1.48    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.60/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f43,f42,f41,f40,f39,f38,f37])).
% 7.60/1.48  
% 7.60/1.48  fof(f76,plain,(
% 7.60/1.48    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f75,plain,(
% 7.60/1.48    sK5 = sK6),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f68,plain,(
% 7.60/1.48    m1_pre_topc(sK3,sK0)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f72,plain,(
% 7.60/1.48    m1_pre_topc(sK2,sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f8,axiom,(
% 7.60/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f27,plain,(
% 7.60/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.60/1.48    inference(ennf_transformation,[],[f8])).
% 7.60/1.48  
% 7.60/1.48  fof(f55,plain,(
% 7.60/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f27])).
% 7.60/1.48  
% 7.60/1.48  fof(f71,plain,(
% 7.60/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f6,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f23,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f6])).
% 7.60/1.48  
% 7.60/1.48  fof(f24,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f23])).
% 7.60/1.48  
% 7.60/1.48  fof(f51,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f24])).
% 7.60/1.48  
% 7.60/1.48  fof(f11,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f32,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f11])).
% 7.60/1.48  
% 7.60/1.48  fof(f33,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.60/1.48    inference(flattening,[],[f32])).
% 7.60/1.48  
% 7.60/1.48  fof(f58,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f33])).
% 7.60/1.48  
% 7.60/1.48  fof(f62,plain,(
% 7.60/1.48    ~v2_struct_0(sK1)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f63,plain,(
% 7.60/1.48    v2_pre_topc(sK1)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f64,plain,(
% 7.60/1.48    l1_pre_topc(sK1)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f69,plain,(
% 7.60/1.48    v1_funct_1(sK4)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f70,plain,(
% 7.60/1.48    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f59,plain,(
% 7.60/1.48    ~v2_struct_0(sK0)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f60,plain,(
% 7.60/1.48    v2_pre_topc(sK0)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f61,plain,(
% 7.60/1.48    l1_pre_topc(sK0)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f5,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f21,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f5])).
% 7.60/1.48  
% 7.60/1.48  fof(f22,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f21])).
% 7.60/1.48  
% 7.60/1.48  fof(f50,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f22])).
% 7.60/1.48  
% 7.60/1.48  fof(f7,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f25,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f7])).
% 7.60/1.48  
% 7.60/1.48  fof(f26,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f25])).
% 7.60/1.48  
% 7.60/1.48  fof(f54,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f26])).
% 7.60/1.48  
% 7.60/1.48  fof(f52,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f26])).
% 7.60/1.48  
% 7.60/1.48  fof(f53,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f26])).
% 7.60/1.48  
% 7.60/1.48  fof(f67,plain,(
% 7.60/1.48    ~v2_struct_0(sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f3,axiom,(
% 7.60/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f18,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.60/1.48    inference(ennf_transformation,[],[f3])).
% 7.60/1.48  
% 7.60/1.48  fof(f48,plain,(
% 7.60/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f18])).
% 7.60/1.48  
% 7.60/1.48  fof(f2,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f16,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f2])).
% 7.60/1.48  
% 7.60/1.48  fof(f17,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.60/1.48    inference(flattening,[],[f16])).
% 7.60/1.48  
% 7.60/1.48  fof(f47,plain,(
% 7.60/1.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f17])).
% 7.60/1.48  
% 7.60/1.48  fof(f10,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f30,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f10])).
% 7.60/1.48  
% 7.60/1.48  fof(f31,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f30])).
% 7.60/1.48  
% 7.60/1.48  fof(f57,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f31])).
% 7.60/1.48  
% 7.60/1.48  fof(f65,plain,(
% 7.60/1.48    ~v2_struct_0(sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f66,plain,(
% 7.60/1.48    m1_pre_topc(sK2,sK0)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f1,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f14,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.60/1.48    inference(ennf_transformation,[],[f1])).
% 7.60/1.48  
% 7.60/1.48  fof(f15,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.60/1.48    inference(flattening,[],[f14])).
% 7.60/1.48  
% 7.60/1.48  fof(f36,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.60/1.48    inference(nnf_transformation,[],[f15])).
% 7.60/1.48  
% 7.60/1.48  fof(f45,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f36])).
% 7.60/1.48  
% 7.60/1.48  fof(f9,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f28,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f9])).
% 7.60/1.48  
% 7.60/1.48  fof(f29,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f28])).
% 7.60/1.48  
% 7.60/1.48  fof(f56,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f29])).
% 7.60/1.48  
% 7.60/1.48  fof(f79,plain,(
% 7.60/1.48    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(equality_resolution,[],[f56])).
% 7.60/1.48  
% 7.60/1.48  fof(f4,axiom,(
% 7.60/1.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f19,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f4])).
% 7.60/1.48  
% 7.60/1.48  fof(f20,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.60/1.48    inference(flattening,[],[f19])).
% 7.60/1.48  
% 7.60/1.48  fof(f49,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f20])).
% 7.60/1.48  
% 7.60/1.48  fof(f77,plain,(
% 7.60/1.48    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f74,plain,(
% 7.60/1.48    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.60/1.48    inference(cnf_transformation,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  cnf(c_15,negated_conjecture,
% 7.60/1.48      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 7.60/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_416,negated_conjecture,
% 7.60/1.48      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_15]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_997,plain,
% 7.60/1.48      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_16,negated_conjecture,
% 7.60/1.48      ( sK5 = sK6 ),
% 7.60/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_415,negated_conjecture,
% 7.60/1.48      ( sK5 = sK6 ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_16]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1053,plain,
% 7.60/1.48      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_997,c_415]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_23,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK3,sK0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_408,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK3,sK0) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1004,plain,
% 7.60/1.48      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_19,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK2,sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_412,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK2,sK3) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_19]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1000,plain,
% 7.60/1.48      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10,plain,
% 7.60/1.48      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_421,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X0_50) | ~ l1_pre_topc(X0_50) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_992,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_20,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.60/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_411,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_20]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1001,plain,
% 7.60/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X3,X4)
% 7.60/1.48      | ~ m1_pre_topc(X3,X1)
% 7.60/1.48      | ~ m1_pre_topc(X1,X4)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ l1_pre_topc(X4)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X4)
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_425,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X2_50,X0_50)
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X3_50)
% 7.60/1.48      | ~ m1_pre_topc(X2_50,X3_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X3_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X3_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X3_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51)
% 7.60/1.48      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_988,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_13,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.60/1.48      | ~ m1_pre_topc(X2,X0)
% 7.60/1.48      | m1_pre_topc(X2,X1)
% 7.60/1.48      | ~ l1_pre_topc(X1)
% 7.60/1.48      | ~ v2_pre_topc(X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_418,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0_50,X1_50)
% 7.60/1.48      | ~ m1_pre_topc(X2_50,X0_50)
% 7.60/1.48      | m1_pre_topc(X2_50,X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_13]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_995,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1225,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(forward_subsumption_resolution,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_988,c_995]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3220,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 7.60/1.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1001,c_1225]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_29,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_36,plain,
% 7.60/1.48      ( v2_struct_0(sK1) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_28,negated_conjecture,
% 7.60/1.48      ( v2_pre_topc(sK1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_37,plain,
% 7.60/1.48      ( v2_pre_topc(sK1) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_27,negated_conjecture,
% 7.60/1.48      ( l1_pre_topc(sK1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_38,plain,
% 7.60/1.48      ( l1_pre_topc(sK1) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_22,negated_conjecture,
% 7.60/1.48      ( v1_funct_1(sK4) ),
% 7.60/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_43,plain,
% 7.60/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_21,negated_conjecture,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_44,plain,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3495,plain,
% 7.60/1.48      ( l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_3220,c_36,c_37,c_38,c_43,c_44]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3496,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_3495]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3507,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_992,c_3496]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_32,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_33,plain,
% 7.60/1.48      ( v2_struct_0(sK0) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_31,negated_conjecture,
% 7.60/1.48      ( v2_pre_topc(sK0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_34,plain,
% 7.60/1.48      ( v2_pre_topc(sK0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_30,negated_conjecture,
% 7.60/1.48      ( l1_pre_topc(sK0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_35,plain,
% 7.60/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3609,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(sK0,sK1,sK0,X0_50,sK4) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_3507,c_33,c_34,c_35]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3610,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(sK0,sK1,sK0,X0_50,sK4)
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_3609]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3617,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1004,c_3610]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X3,X1)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ l1_pre_topc(X1)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X1)
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_426,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X2_50,X0_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X0_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X0_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X0_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51)
% 7.60/1.48      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_987,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2412,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 7.60/1.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1001,c_987]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2991,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,sK0) != iProver_top
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_2412,c_33,c_34,c_35,c_36,c_37,c_38,c_43,c_44]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2992,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50)
% 7.60/1.48      | m1_pre_topc(X0_50,sK0) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_2991]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2999,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1004,c_2992]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3629,plain,
% 7.60/1.48      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_3617,c_2999]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X3,X4)
% 7.60/1.48      | ~ m1_pre_topc(X1,X4)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ l1_pre_topc(X4)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X4)
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v1_funct_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_424,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X2_50)
% 7.60/1.48      | ~ m1_pre_topc(X3_50,X2_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X2_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X2_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X2_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_989,plain,
% 7.60/1.48      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3731,plain,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_3629,c_989]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_42,plain,
% 7.60/1.48      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_45,plain,
% 7.60/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_58,plain,
% 7.60/1.48      ( m1_pre_topc(X0,X0) = iProver_top
% 7.60/1.48      | l1_pre_topc(X0) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_60,plain,
% 7.60/1.48      ( m1_pre_topc(sK0,sK0) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_58]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4799,plain,
% 7.60/1.48      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_3731,c_33,c_34,c_35,c_36,c_37,c_38,c_42,c_43,c_44,
% 7.60/1.48                 c_45,c_60]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4804,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.60/1.48      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,sK3) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4799,c_1225]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_59,plain,
% 7.60/1.48      ( m1_pre_topc(sK0,sK0) | ~ l1_pre_topc(sK0) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_433,plain,( X0_51 = X0_51 ),theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_450,plain,
% 7.60/1.48      ( sK4 = sK4 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_433]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_439,plain,
% 7.60/1.48      ( X0_51 != X1_51
% 7.60/1.48      | k2_tmap_1(X0_50,X1_50,X0_51,X2_50) = k2_tmap_1(X0_50,X1_50,X1_51,X2_50) ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2144,plain,
% 7.60/1.48      ( X0_51 != sK4
% 7.60/1.48      | k2_tmap_1(sK0,sK1,X0_51,sK3) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_439]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2147,plain,
% 7.60/1.48      ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 7.60/1.48      | sK4 != sK4 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2144]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1417,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(X0_50,sK0)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(sK0)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(sK0)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(sK0)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | ~ v1_funct_1(sK4)
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k2_tmap_1(sK0,sK1,sK4,X0_50) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_426]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2149,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(sK3,sK0)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(sK0)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(sK0)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(sK0)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | ~ v1_funct_1(sK4)
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1417]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_438,plain,
% 7.60/1.48      ( ~ v1_funct_1(X0_51) | v1_funct_1(X1_51) | X1_51 != X0_51 ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2525,plain,
% 7.60/1.48      ( ~ v1_funct_1(X0_51)
% 7.60/1.48      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)))
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != X0_51 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_438]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3058,plain,
% 7.60/1.48      ( ~ v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4))
% 7.60/1.48      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)))
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k3_tmap_1(X0_50,sK1,sK0,sK3,sK4) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2525]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3060,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k3_tmap_1(X0_50,sK1,sK0,sK3,sK4)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4)) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_3058]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3062,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))) = iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_3060]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1432,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X1_50)
% 7.60/1.48      | ~ m1_pre_topc(X0_50,sK0)
% 7.60/1.48      | ~ m1_pre_topc(sK0,X1_50)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | ~ v1_funct_1(sK4)
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_425]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3059,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(sK3,X0_50)
% 7.60/1.48      | ~ m1_pre_topc(sK3,sK0)
% 7.60/1.48      | ~ m1_pre_topc(sK0,X0_50)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(X0_50)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(X0_50)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(X0_50)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | ~ v1_funct_1(sK4)
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_50,sK1,sK0,sK3,sK4) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1432]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3065,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(sK3,sK0)
% 7.60/1.48      | ~ m1_pre_topc(sK0,sK0)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(sK0)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(sK0)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(sK0)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | ~ v1_funct_1(sK4)
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_3059]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_434,plain,
% 7.60/1.48      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 7.60/1.48      theory(equality) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2346,plain,
% 7.60/1.48      ( X0_51 != X1_51
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) != X1_51
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) = X0_51 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_434]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2812,plain,
% 7.60/1.48      ( X0_51 != k2_tmap_1(sK0,sK1,X1_51,sK3)
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) = X0_51
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) != k2_tmap_1(sK0,sK1,X1_51,sK3) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2346]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3304,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) != k2_tmap_1(sK0,sK1,sK4,sK3)
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) != k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2812]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_9,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X3,X4)
% 7.60/1.48      | ~ m1_pre_topc(X1,X4)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ l1_pre_topc(X4)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X4)
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_422,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X2_50)
% 7.60/1.48      | ~ m1_pre_topc(X3_50,X2_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X2_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X2_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X2_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1412,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X1_50)
% 7.60/1.48      | ~ m1_pre_topc(sK0,X1_50)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4))
% 7.60/1.48      | ~ v1_funct_1(sK4) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_422]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3455,plain,
% 7.60/1.48      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.60/1.48      | ~ m1_pre_topc(sK3,X0_50)
% 7.60/1.48      | ~ m1_pre_topc(sK0,X0_50)
% 7.60/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.60/1.48      | v2_struct_0(X0_50)
% 7.60/1.48      | v2_struct_0(sK1)
% 7.60/1.48      | ~ l1_pre_topc(X0_50)
% 7.60/1.48      | ~ l1_pre_topc(sK1)
% 7.60/1.48      | ~ v2_pre_topc(X0_50)
% 7.60/1.48      | ~ v2_pre_topc(sK1)
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4))
% 7.60/1.48      | ~ v1_funct_1(sK4) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_1412]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3456,plain,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X0_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X0_50) != iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X0_50,sK1,sK0,sK3,sK4)) = iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_3455]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3458,plain,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_3456]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2332,plain,
% 7.60/1.48      ( ~ v1_funct_1(X0_51)
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) != X0_51 ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_438]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3513,plain,
% 7.60/1.48      ( ~ v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)))
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.60/1.48      | k2_tmap_1(sK0,sK1,sK4,sK3) != k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_2332]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3514,plain,
% 7.60/1.48      ( k2_tmap_1(sK0,sK1,sK4,sK3) != k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
% 7.60/1.48      | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_3513]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_8,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.60/1.48      | ~ m1_pre_topc(X4,X3)
% 7.60/1.48      | ~ m1_pre_topc(X1,X3)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.60/1.48      | v2_struct_0(X3)
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | ~ l1_pre_topc(X3)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X3)
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v1_funct_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_423,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X3_50,X2_50)
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X2_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X2_50)
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X2_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X2_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_990,plain,
% 7.60/1.48      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 7.60/1.48      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X2_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3732,plain,
% 7.60/1.48      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 7.60/1.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_3629,c_990]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5816,plain,
% 7.60/1.48      ( l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.60/1.48      | m1_pre_topc(X0_50,sK3) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_4804,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,
% 7.60/1.48                 c_37,c_27,c_38,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,
% 7.60/1.48                 c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,
% 7.60/1.48                 c_3458,c_3514,c_3732]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5817,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.60/1.48      | m1_pre_topc(X0_50,sK3) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_5816]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5828,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.60/1.48      | m1_pre_topc(sK3,X0_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1000,c_5817]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4806,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
% 7.60/1.48      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,sK3) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4799,c_987]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_24,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK3) ),
% 7.60/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_41,plain,
% 7.60/1.48      ( v2_struct_0(sK3) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_428,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0_50,X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | l1_pre_topc(X0_50) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_985,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2023,plain,
% 7.60/1.48      ( l1_pre_topc(sK3) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1004,c_985]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.60/1.48      | ~ l1_pre_topc(X1)
% 7.60/1.48      | ~ v2_pre_topc(X1)
% 7.60/1.48      | v2_pre_topc(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_429,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0_50,X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | v2_pre_topc(X0_50) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_984,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2064,plain,
% 7.60/1.48      ( l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) = iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1004,c_984]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5655,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,sK3) != iProver_top
% 7.60/1.48      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_4806,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,
% 7.60/1.48                 c_37,c_27,c_38,c_41,c_23,c_42,c_22,c_43,c_21,c_44,c_20,
% 7.60/1.48                 c_45,c_59,c_60,c_450,c_2023,c_2064,c_2147,c_2149,c_3062,
% 7.60/1.48                 c_3065,c_3304,c_3458,c_3514,c_3732]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5656,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_50)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_50)
% 7.60/1.48      | m1_pre_topc(X0_50,sK3) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_5655]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5663,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1000,c_5656]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5847,plain,
% 7.60/1.48      ( k3_tmap_1(X0_50,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 7.60/1.48      | m1_pre_topc(sK3,X0_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) != iProver_top ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_5828,c_5663]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6018,plain,
% 7.60/1.48      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1004,c_5847]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5857,plain,
% 7.60/1.48      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top ),
% 7.60/1.48      inference(instantiation,[status(thm)],[c_5847]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6317,plain,
% 7.60/1.48      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6018,c_33,c_34,c_35,c_42,c_5857]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_12,plain,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 7.60/1.48      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 7.60/1.48      | ~ m1_pre_topc(X3,X2)
% 7.60/1.48      | ~ m1_pre_topc(X0,X2)
% 7.60/1.48      | ~ m1_pre_topc(X0,X3)
% 7.60/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.60/1.48      | v2_struct_0(X2)
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | v2_struct_0(X3)
% 7.60/1.48      | v2_struct_0(X0)
% 7.60/1.48      | ~ l1_pre_topc(X2)
% 7.60/1.48      | ~ l1_pre_topc(X1)
% 7.60/1.48      | ~ v2_pre_topc(X2)
% 7.60/1.48      | ~ v2_pre_topc(X1)
% 7.60/1.48      | ~ v1_funct_1(X4) ),
% 7.60/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_419,plain,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50))
% 7.60/1.48      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X3_50,X2_50)
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X2_50)
% 7.60/1.48      | ~ m1_pre_topc(X0_50,X3_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X2_50)
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X3_50)
% 7.60/1.48      | v2_struct_0(X0_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X2_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X2_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_12]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_994,plain,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) = iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X2_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1283,plain,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k3_tmap_1(X2_50,X1_50,X3_50,X0_50,k2_tmap_1(X2_50,X1_50,X0_51,X3_50)),k2_tmap_1(X2_50,X1_50,X0_51,X0_50)) = iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X2_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X3_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X2_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X2_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(forward_subsumption_resolution,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_994,c_995]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6320,plain,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 7.60/1.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_6317,c_1283]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_26,negated_conjecture,
% 7.60/1.48      ( ~ v2_struct_0(sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_39,plain,
% 7.60/1.48      ( v2_struct_0(sK2) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_46,plain,
% 7.60/1.48      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6855,plain,
% 7.60/1.48      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6320,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_41,c_42,
% 7.60/1.48                 c_43,c_44,c_45,c_46]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6321,plain,
% 7.60/1.48      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_6317,c_989]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_25,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_40,plain,
% 7.60/1.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6747,plain,
% 7.60/1.48      ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6321,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,
% 7.60/1.48                 c_37,c_27,c_38,c_40,c_23,c_42,c_22,c_43,c_21,c_44,c_20,
% 7.60/1.48                 c_45,c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,
% 7.60/1.48                 c_3458,c_3514,c_3731,c_3732]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1,plain,
% 7.60/1.48      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.60/1.48      | ~ v1_funct_2(X3,X0,X1)
% 7.60/1.48      | ~ v1_funct_2(X2,X0,X1)
% 7.60/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.48      | ~ v1_funct_1(X3)
% 7.60/1.48      | ~ v1_funct_1(X2)
% 7.60/1.48      | X2 = X3 ),
% 7.60/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_430,plain,
% 7.60/1.48      ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
% 7.60/1.48      | ~ v1_funct_2(X1_51,X0_52,X1_52)
% 7.60/1.48      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 7.60/1.48      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 7.60/1.48      | ~ v1_funct_1(X0_51)
% 7.60/1.48      | ~ v1_funct_1(X1_51)
% 7.60/1.48      | X0_51 = X1_51 ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_983,plain,
% 7.60/1.48      ( X0_51 = X1_51
% 7.60/1.48      | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 7.60/1.48      | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top
% 7.60/1.48      | v1_funct_1(X1_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6755,plain,
% 7.60/1.48      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
% 7.60/1.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_6747,c_983]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6323,plain,
% 7.60/1.48      ( v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.60/1.48      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_6317,c_990]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_991,plain,
% 7.60/1.48      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X3_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X3_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4805,plain,
% 7.60/1.48      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_4799,c_991]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5537,plain,
% 7.60/1.48      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_4805,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,
% 7.60/1.48                 c_37,c_27,c_38,c_23,c_42,c_22,c_43,c_21,c_44,c_20,c_45,
% 7.60/1.48                 c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,
% 7.60/1.48                 c_3458,c_3514,c_3732]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5538,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK3,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK3,X0_50,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_5537]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6324,plain,
% 7.60/1.48      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_6317,c_5538]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7125,plain,
% 7.60/1.48      ( v1_funct_1(X0_51) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
% 7.60/1.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_6755,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,
% 7.60/1.48                 c_37,c_27,c_38,c_40,c_23,c_42,c_22,c_43,c_21,c_44,c_20,
% 7.60/1.48                 c_45,c_59,c_60,c_450,c_2147,c_2149,c_3062,c_3065,c_3304,
% 7.60/1.48                 c_3458,c_3514,c_3731,c_3732,c_6323,c_6324]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7126,plain,
% 7.60/1.48      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_51
% 7.60/1.48      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_51) != iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_7125]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7136,plain,
% 7.60/1.48      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 7.60/1.48      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_6855,c_7126]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_406,negated_conjecture,
% 7.60/1.48      ( m1_pre_topc(sK2,sK0) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_25]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1006,plain,
% 7.60/1.48      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3618,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1006,c_3610]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3000,plain,
% 7.60/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1006,c_2992]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3626,plain,
% 7.60/1.48      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 7.60/1.48      inference(light_normalisation,[status(thm)],[c_3618,c_3000]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3664,plain,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_3626,c_989]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3665,plain,
% 7.60/1.48      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.60/1.48      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.60/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_3626,c_990]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2507,plain,
% 7.60/1.48      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 7.60/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1001,c_991]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3195,plain,
% 7.60/1.48      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_2507,c_36,c_37,c_38,c_43,c_44]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3196,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK0,X1_50) != iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK0,X0_50,sK4)) = iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_3195]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3666,plain,
% 7.60/1.48      ( m1_pre_topc(sK0,sK0) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.60/1.48      | v2_struct_0(sK0) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK0) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_3626,c_3196]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7148,plain,
% 7.60/1.48      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7136,c_33,c_34,c_35,c_36,c_37,c_38,c_40,c_43,c_44,
% 7.60/1.48                 c_45,c_60,c_3664,c_3665,c_3666]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_11,plain,
% 7.60/1.48      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 7.60/1.48      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.60/1.48      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.60/1.48      | ~ m1_pre_topc(X4,X0)
% 7.60/1.48      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.60/1.48      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.60/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | v2_struct_0(X0)
% 7.60/1.48      | v2_struct_0(X4)
% 7.60/1.48      | ~ l1_pre_topc(X1)
% 7.60/1.48      | ~ l1_pre_topc(X0)
% 7.60/1.48      | ~ v2_pre_topc(X1)
% 7.60/1.48      | ~ v2_pre_topc(X0)
% 7.60/1.48      | ~ v1_funct_1(X2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_420,plain,
% 7.60/1.48      ( ~ r1_tmap_1(X0_50,X1_50,X0_51,X1_51)
% 7.60/1.48      | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51)
% 7.60/1.48      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 7.60/1.48      | ~ m1_pre_topc(X2_50,X0_50)
% 7.60/1.48      | ~ m1_subset_1(X1_51,u1_struct_0(X2_50))
% 7.60/1.48      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 7.60/1.48      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 7.60/1.48      | v2_struct_0(X2_50)
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X0_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50)
% 7.60/1.48      | ~ l1_pre_topc(X0_50)
% 7.60/1.48      | ~ v2_pre_topc(X1_50)
% 7.60/1.48      | ~ v2_pre_topc(X0_50)
% 7.60/1.48      | ~ v1_funct_1(X0_51) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_993,plain,
% 7.60/1.48      ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
% 7.60/1.48      | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_51,u1_struct_0(X0_50)) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X2_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_4,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.60/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.60/1.48      | m1_subset_1(X2,u1_struct_0(X1))
% 7.60/1.48      | v2_struct_0(X1)
% 7.60/1.48      | v2_struct_0(X0)
% 7.60/1.48      | ~ l1_pre_topc(X1) ),
% 7.60/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_427,plain,
% 7.60/1.48      ( ~ m1_pre_topc(X0_50,X1_50)
% 7.60/1.48      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 7.60/1.48      | m1_subset_1(X0_51,u1_struct_0(X1_50))
% 7.60/1.48      | v2_struct_0(X1_50)
% 7.60/1.48      | v2_struct_0(X0_50)
% 7.60/1.48      | ~ l1_pre_topc(X1_50) ),
% 7.60/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_986,plain,
% 7.60/1.48      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,u1_struct_0(X1_50)) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1253,plain,
% 7.60/1.48      ( r1_tmap_1(X0_50,X1_50,X0_51,X1_51) != iProver_top
% 7.60/1.48      | r1_tmap_1(X2_50,X1_50,k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 7.60/1.48      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 7.60/1.48      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 7.60/1.48      | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 7.60/1.48      | v2_struct_0(X2_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X1_50) = iProver_top
% 7.60/1.48      | v2_struct_0(X0_50) = iProver_top
% 7.60/1.48      | l1_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | l1_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X1_50) != iProver_top
% 7.60/1.48      | v2_pre_topc(X0_50) != iProver_top
% 7.60/1.48      | v1_funct_1(X0_51) != iProver_top ),
% 7.60/1.48      inference(forward_subsumption_resolution,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_993,c_986]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_7181,plain,
% 7.60/1.48      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
% 7.60/1.48      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 7.60/1.48      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.60/1.48      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 7.60/1.48      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.60/1.48      | v2_struct_0(sK3) = iProver_top
% 7.60/1.48      | v2_struct_0(sK1) = iProver_top
% 7.60/1.48      | v2_struct_0(sK2) = iProver_top
% 7.60/1.48      | l1_pre_topc(sK3) != iProver_top
% 7.60/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK3) != iProver_top
% 7.60/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.60/1.48      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_7148,c_1253]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_25924,plain,
% 7.60/1.48      ( m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 7.60/1.48      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 7.60/1.48      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_7181,c_32,c_33,c_31,c_34,c_30,c_35,c_29,c_36,c_28,
% 7.60/1.48                 c_37,c_27,c_38,c_39,c_41,c_23,c_42,c_22,c_43,c_21,c_44,
% 7.60/1.48                 c_20,c_45,c_46,c_59,c_60,c_450,c_2023,c_2064,c_2147,
% 7.60/1.48                 c_2149,c_3062,c_3065,c_3304,c_3458,c_3514,c_3731,c_3732]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_25925,plain,
% 7.60/1.48      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) != iProver_top
% 7.60/1.48      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_51) = iProver_top
% 7.60/1.48      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_25924]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_25934,plain,
% 7.60/1.48      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
% 7.60/1.48      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1053,c_25925]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_14,negated_conjecture,
% 7.60/1.48      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
% 7.60/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_50,plain,
% 7.60/1.48      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_17,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_48,plain,
% 7.60/1.48      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(contradiction,plain,
% 7.60/1.48      ( $false ),
% 7.60/1.48      inference(minisat,[status(thm)],[c_25934,c_50,c_48]) ).
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  ------                               Statistics
% 7.60/1.48  
% 7.60/1.48  ------ General
% 7.60/1.48  
% 7.60/1.48  abstr_ref_over_cycles:                  0
% 7.60/1.48  abstr_ref_under_cycles:                 0
% 7.60/1.48  gc_basic_clause_elim:                   0
% 7.60/1.48  forced_gc_time:                         0
% 7.60/1.48  parsing_time:                           0.017
% 7.60/1.48  unif_index_cands_time:                  0.
% 7.60/1.48  unif_index_add_time:                    0.
% 7.60/1.48  orderings_time:                         0.
% 7.60/1.48  out_proof_time:                         0.018
% 7.60/1.48  total_time:                             0.914
% 7.60/1.48  num_of_symbols:                         54
% 7.60/1.48  num_of_terms:                           10749
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing
% 7.60/1.48  
% 7.60/1.48  num_of_splits:                          0
% 7.60/1.48  num_of_split_atoms:                     0
% 7.60/1.48  num_of_reused_defs:                     0
% 7.60/1.48  num_eq_ax_congr_red:                    32
% 7.60/1.48  num_of_sem_filtered_clauses:            1
% 7.60/1.48  num_of_subtypes:                        4
% 7.60/1.48  monotx_restored_types:                  0
% 7.60/1.48  sat_num_of_epr_types:                   0
% 7.60/1.48  sat_num_of_non_cyclic_types:            0
% 7.60/1.48  sat_guarded_non_collapsed_types:        1
% 7.60/1.48  num_pure_diseq_elim:                    0
% 7.60/1.48  simp_replaced_by:                       0
% 7.60/1.48  res_preprocessed:                       118
% 7.60/1.48  prep_upred:                             0
% 7.60/1.48  prep_unflattend:                        8
% 7.60/1.48  smt_new_axioms:                         0
% 7.60/1.48  pred_elim_cands:                        9
% 7.60/1.48  pred_elim:                              0
% 7.60/1.48  pred_elim_cl:                           0
% 7.60/1.48  pred_elim_cycles:                       1
% 7.60/1.48  merged_defs:                            0
% 7.60/1.48  merged_defs_ncl:                        0
% 7.60/1.48  bin_hyper_res:                          0
% 7.60/1.48  prep_cycles:                            3
% 7.60/1.48  pred_elim_time:                         0.006
% 7.60/1.48  splitting_time:                         0.
% 7.60/1.48  sem_filter_time:                        0.
% 7.60/1.48  monotx_time:                            0.
% 7.60/1.48  subtype_inf_time:                       0.002
% 7.60/1.48  
% 7.60/1.48  ------ Problem properties
% 7.60/1.48  
% 7.60/1.48  clauses:                                33
% 7.60/1.48  conjectures:                            19
% 7.60/1.48  epr:                                    17
% 7.60/1.48  horn:                                   25
% 7.60/1.48  ground:                                 19
% 7.60/1.48  unary:                                  19
% 7.60/1.48  binary:                                 1
% 7.60/1.48  lits:                                   141
% 7.60/1.48  lits_eq:                                4
% 7.60/1.48  fd_pure:                                0
% 7.60/1.48  fd_pseudo:                              0
% 7.60/1.48  fd_cond:                                0
% 7.60/1.48  fd_pseudo_cond:                         1
% 7.60/1.48  ac_symbols:                             0
% 7.60/1.48  
% 7.60/1.48  ------ Propositional Solver
% 7.60/1.48  
% 7.60/1.48  prop_solver_calls:                      30
% 7.60/1.48  prop_fast_solver_calls:                 3885
% 7.60/1.48  smt_solver_calls:                       0
% 7.60/1.48  smt_fast_solver_calls:                  0
% 7.60/1.48  prop_num_of_clauses:                    5359
% 7.60/1.48  prop_preprocess_simplified:             13059
% 7.60/1.48  prop_fo_subsumed:                       1190
% 7.60/1.48  prop_solver_time:                       0.
% 7.60/1.48  smt_solver_time:                        0.
% 7.60/1.48  smt_fast_solver_time:                   0.
% 7.60/1.48  prop_fast_solver_time:                  0.
% 7.60/1.48  prop_unsat_core_time:                   0.001
% 7.60/1.48  
% 7.60/1.48  ------ QBF
% 7.60/1.48  
% 7.60/1.48  qbf_q_res:                              0
% 7.60/1.48  qbf_num_tautologies:                    0
% 7.60/1.48  qbf_prep_cycles:                        0
% 7.60/1.48  
% 7.60/1.48  ------ BMC1
% 7.60/1.48  
% 7.60/1.48  bmc1_current_bound:                     -1
% 7.60/1.48  bmc1_last_solved_bound:                 -1
% 7.60/1.48  bmc1_unsat_core_size:                   -1
% 7.60/1.48  bmc1_unsat_core_parents_size:           -1
% 7.60/1.48  bmc1_merge_next_fun:                    0
% 7.60/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.60/1.48  
% 7.60/1.48  ------ Instantiation
% 7.60/1.48  
% 7.60/1.48  inst_num_of_clauses:                    1772
% 7.60/1.48  inst_num_in_passive:                    362
% 7.60/1.48  inst_num_in_active:                     1117
% 7.60/1.48  inst_num_in_unprocessed:                293
% 7.60/1.48  inst_num_of_loops:                      1220
% 7.60/1.48  inst_num_of_learning_restarts:          0
% 7.60/1.48  inst_num_moves_active_passive:          93
% 7.60/1.48  inst_lit_activity:                      0
% 7.60/1.48  inst_lit_activity_moves:                0
% 7.60/1.48  inst_num_tautologies:                   0
% 7.60/1.48  inst_num_prop_implied:                  0
% 7.60/1.48  inst_num_existing_simplified:           0
% 7.60/1.48  inst_num_eq_res_simplified:             0
% 7.60/1.48  inst_num_child_elim:                    0
% 7.60/1.48  inst_num_of_dismatching_blockings:      2058
% 7.60/1.48  inst_num_of_non_proper_insts:           3945
% 7.60/1.48  inst_num_of_duplicates:                 0
% 7.60/1.48  inst_inst_num_from_inst_to_res:         0
% 7.60/1.48  inst_dismatching_checking_time:         0.
% 7.60/1.48  
% 7.60/1.48  ------ Resolution
% 7.60/1.48  
% 7.60/1.48  res_num_of_clauses:                     0
% 7.60/1.48  res_num_in_passive:                     0
% 7.60/1.48  res_num_in_active:                      0
% 7.60/1.48  res_num_of_loops:                       121
% 7.60/1.48  res_forward_subset_subsumed:            443
% 7.60/1.48  res_backward_subset_subsumed:           2
% 7.60/1.48  res_forward_subsumed:                   0
% 7.60/1.48  res_backward_subsumed:                  0
% 7.60/1.48  res_forward_subsumption_resolution:     1
% 7.60/1.48  res_backward_subsumption_resolution:    0
% 7.60/1.48  res_clause_to_clause_subsumption:       1390
% 7.60/1.48  res_orphan_elimination:                 0
% 7.60/1.48  res_tautology_del:                      520
% 7.60/1.48  res_num_eq_res_simplified:              0
% 7.60/1.48  res_num_sel_changes:                    0
% 7.60/1.48  res_moves_from_active_to_pass:          0
% 7.60/1.48  
% 7.60/1.48  ------ Superposition
% 7.60/1.48  
% 7.60/1.48  sup_time_total:                         0.
% 7.60/1.48  sup_time_generating:                    0.
% 7.60/1.48  sup_time_sim_full:                      0.
% 7.60/1.48  sup_time_sim_immed:                     0.
% 7.60/1.48  
% 7.60/1.48  sup_num_of_clauses:                     299
% 7.60/1.48  sup_num_in_active:                      199
% 7.60/1.48  sup_num_in_passive:                     100
% 7.60/1.48  sup_num_of_loops:                       243
% 7.60/1.48  sup_fw_superposition:                   201
% 7.60/1.48  sup_bw_superposition:                   266
% 7.60/1.48  sup_immediate_simplified:               111
% 7.60/1.48  sup_given_eliminated:                   0
% 7.60/1.48  comparisons_done:                       0
% 7.60/1.48  comparisons_avoided:                    0
% 7.60/1.48  
% 7.60/1.48  ------ Simplifications
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  sim_fw_subset_subsumed:                 37
% 7.60/1.48  sim_bw_subset_subsumed:                 9
% 7.60/1.48  sim_fw_subsumed:                        33
% 7.60/1.48  sim_bw_subsumed:                        0
% 7.60/1.48  sim_fw_subsumption_res:                 17
% 7.60/1.48  sim_bw_subsumption_res:                 1
% 7.60/1.48  sim_tautology_del:                      13
% 7.60/1.48  sim_eq_tautology_del:                   11
% 7.60/1.48  sim_eq_res_simp:                        0
% 7.60/1.48  sim_fw_demodulated:                     26
% 7.60/1.48  sim_bw_demodulated:                     45
% 7.60/1.48  sim_light_normalised:                   55
% 7.60/1.48  sim_joinable_taut:                      0
% 7.60/1.48  sim_joinable_simp:                      0
% 7.60/1.48  sim_ac_normalised:                      0
% 7.60/1.48  sim_smt_subsumption:                    0
% 7.60/1.48  
%------------------------------------------------------------------------------
