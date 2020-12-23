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
% DateTime   : Thu Dec  3 12:23:26 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 854 expanded)
%              Number of clauses        :  105 ( 184 expanded)
%              Number of leaves         :   24 ( 374 expanded)
%              Depth                    :   26
%              Number of atoms          : 1179 (11963 expanded)
%              Number of equality atoms :  278 (1806 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10)
        & sK10 = X5
        & m1_subset_1(sK10,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK9)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK9 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
                ( ~ r1_tmap_1(X3,X1,sK8,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
                    ( ~ r1_tmap_1(sK7,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK7)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                        & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK6)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                            ( ~ r1_tmap_1(X3,sK5,X4,X5)
                            & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    & sK9 = sK10
    & m1_subset_1(sK10,u1_struct_0(sK6))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f40,f64,f63,f62,f61,f60,f59,f58])).

fof(f105,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f111,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f65])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f84,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f65])).

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

fof(f66,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f41])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f65])).

fof(f114,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f31])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f57,plain,(
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

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f120,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f109,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f65])).

fof(f108,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

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

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f65])).

fof(f110,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f98,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f112,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f65])).

fof(f116,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f65])).

fof(f113,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3092,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3122,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6509,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_3122])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_52,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_53,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_6541,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6509,c_52,c_53])).

cnf(c_37,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_19,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3106,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5502,plain,
    ( v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_3106])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3109,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4962,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_3109])).

cnf(c_5608,plain,
    ( v2_pre_topc(sK6) != iProver_top
    | v1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5502,c_53,c_4962])).

cnf(c_6546,plain,
    ( v1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_6541,c_5608])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3094,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4961,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_3109])).

cnf(c_5101,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4961,c_53])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3123,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5383,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | v1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5101,c_3123])).

cnf(c_6614,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_6546,c_5383])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3105,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6122,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_pre_topc(sK6) = X1
    | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_3105])).

cnf(c_6821,plain,
    ( u1_pre_topc(sK7) = u1_pre_topc(sK6)
    | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6614,c_6122])).

cnf(c_17,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3716,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3721,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3716])).

cnf(c_6121,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_pre_topc(sK6) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_3105])).

cnf(c_6823,plain,
    ( u1_pre_topc(sK7) = u1_pre_topc(sK6)
    | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6614,c_6121])).

cnf(c_7086,plain,
    ( u1_pre_topc(sK7) = u1_pre_topc(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6821,c_53,c_3721,c_4961,c_6823])).

cnf(c_13,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3110,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7117,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7086,c_3110])).

cnf(c_33,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3098,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3161,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3098,c_34])).

cnf(c_14,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_25,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_27,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_274,plain,
    ( ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_27])).

cnf(c_275,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_274])).

cnf(c_594,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_275])).

cnf(c_595,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_599,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_27])).

cnf(c_30,plain,
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
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_729,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_39])).

cnf(c_730,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK8)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_734,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_40])).

cnf(c_735,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_778,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_735,c_29])).

cnf(c_801,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(resolution_lifted,[status(thm)],[c_599,c_778])).

cnf(c_802,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_846,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
    | r1_tmap_1(X3,X1,sK8,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X3) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_802,c_16,c_1])).

cnf(c_3083,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK8),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK8,X4) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_4036,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3083])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_54,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_55,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_56,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4129,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4036,c_54,c_55,c_56])).

cnf(c_4130,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK7)
    | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
    | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4129])).

cnf(c_4147,plain,
    ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4130])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_59,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_63,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4557,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4147,c_59,c_63])).

cnf(c_4558,plain,
    ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4557])).

cnf(c_4574,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_pre_topc(sK7,sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3161,c_4558])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_57,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_60,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_64,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_67,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_3097,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3148,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3097,c_34])).

cnf(c_4688,plain,
    ( m1_pre_topc(sK6,sK7) != iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4574,c_51,c_52,c_53,c_57,c_60,c_64,c_67,c_3148])).

cnf(c_4689,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4688])).

cnf(c_28,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3101,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_281,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_16])).

cnf(c_282,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_3084,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_4155,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_3084])).

cnf(c_4435,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_4155])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7117,c_6509,c_4962,c_4689,c_4435,c_53,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:55:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.78/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/0.96  
% 2.78/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.96  
% 2.78/0.96  ------  iProver source info
% 2.78/0.96  
% 2.78/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.96  git: non_committed_changes: false
% 2.78/0.96  git: last_make_outside_of_git: false
% 2.78/0.96  
% 2.78/0.96  ------ 
% 2.78/0.96  
% 2.78/0.96  ------ Input Options
% 2.78/0.96  
% 2.78/0.96  --out_options                           all
% 2.78/0.96  --tptp_safe_out                         true
% 2.78/0.96  --problem_path                          ""
% 2.78/0.96  --include_path                          ""
% 2.78/0.96  --clausifier                            res/vclausify_rel
% 2.78/0.96  --clausifier_options                    --mode clausify
% 2.78/0.96  --stdin                                 false
% 2.78/0.96  --stats_out                             all
% 2.78/0.96  
% 2.78/0.96  ------ General Options
% 2.78/0.96  
% 2.78/0.96  --fof                                   false
% 2.78/0.96  --time_out_real                         305.
% 2.78/0.96  --time_out_virtual                      -1.
% 2.78/0.96  --symbol_type_check                     false
% 2.78/0.96  --clausify_out                          false
% 2.78/0.96  --sig_cnt_out                           false
% 2.78/0.96  --trig_cnt_out                          false
% 2.78/0.96  --trig_cnt_out_tolerance                1.
% 2.78/0.96  --trig_cnt_out_sk_spl                   false
% 2.78/0.96  --abstr_cl_out                          false
% 2.78/0.96  
% 2.78/0.96  ------ Global Options
% 2.78/0.96  
% 2.78/0.96  --schedule                              default
% 2.78/0.96  --add_important_lit                     false
% 2.78/0.96  --prop_solver_per_cl                    1000
% 2.78/0.96  --min_unsat_core                        false
% 2.78/0.96  --soft_assumptions                      false
% 2.78/0.96  --soft_lemma_size                       3
% 2.78/0.96  --prop_impl_unit_size                   0
% 2.78/0.96  --prop_impl_unit                        []
% 2.78/0.96  --share_sel_clauses                     true
% 2.78/0.96  --reset_solvers                         false
% 2.78/0.96  --bc_imp_inh                            [conj_cone]
% 2.78/0.96  --conj_cone_tolerance                   3.
% 2.78/0.96  --extra_neg_conj                        none
% 2.78/0.96  --large_theory_mode                     true
% 2.78/0.96  --prolific_symb_bound                   200
% 2.78/0.96  --lt_threshold                          2000
% 2.78/0.96  --clause_weak_htbl                      true
% 2.78/0.96  --gc_record_bc_elim                     false
% 2.78/0.96  
% 2.78/0.96  ------ Preprocessing Options
% 2.78/0.96  
% 2.78/0.96  --preprocessing_flag                    true
% 2.78/0.96  --time_out_prep_mult                    0.1
% 2.78/0.96  --splitting_mode                        input
% 2.78/0.96  --splitting_grd                         true
% 2.78/0.96  --splitting_cvd                         false
% 2.78/0.96  --splitting_cvd_svl                     false
% 2.78/0.96  --splitting_nvd                         32
% 2.78/0.96  --sub_typing                            true
% 2.78/0.96  --prep_gs_sim                           true
% 2.78/0.96  --prep_unflatten                        true
% 2.78/0.96  --prep_res_sim                          true
% 2.78/0.96  --prep_upred                            true
% 2.78/0.96  --prep_sem_filter                       exhaustive
% 2.78/0.96  --prep_sem_filter_out                   false
% 2.78/0.96  --pred_elim                             true
% 2.78/0.96  --res_sim_input                         true
% 2.78/0.96  --eq_ax_congr_red                       true
% 2.78/0.96  --pure_diseq_elim                       true
% 2.78/0.96  --brand_transform                       false
% 2.78/0.96  --non_eq_to_eq                          false
% 2.78/0.96  --prep_def_merge                        true
% 2.78/0.96  --prep_def_merge_prop_impl              false
% 2.78/0.96  --prep_def_merge_mbd                    true
% 2.78/0.96  --prep_def_merge_tr_red                 false
% 2.78/0.96  --prep_def_merge_tr_cl                  false
% 2.78/0.96  --smt_preprocessing                     true
% 2.78/0.96  --smt_ac_axioms                         fast
% 2.78/0.96  --preprocessed_out                      false
% 2.78/0.96  --preprocessed_stats                    false
% 2.78/0.96  
% 2.78/0.96  ------ Abstraction refinement Options
% 2.78/0.96  
% 2.78/0.96  --abstr_ref                             []
% 2.78/0.96  --abstr_ref_prep                        false
% 2.78/0.96  --abstr_ref_until_sat                   false
% 2.78/0.96  --abstr_ref_sig_restrict                funpre
% 2.78/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.96  --abstr_ref_under                       []
% 2.78/0.96  
% 2.78/0.96  ------ SAT Options
% 2.78/0.96  
% 2.78/0.96  --sat_mode                              false
% 2.78/0.96  --sat_fm_restart_options                ""
% 2.78/0.96  --sat_gr_def                            false
% 2.78/0.96  --sat_epr_types                         true
% 2.78/0.96  --sat_non_cyclic_types                  false
% 2.78/0.96  --sat_finite_models                     false
% 2.78/0.96  --sat_fm_lemmas                         false
% 2.78/0.96  --sat_fm_prep                           false
% 2.78/0.96  --sat_fm_uc_incr                        true
% 2.78/0.96  --sat_out_model                         small
% 2.78/0.96  --sat_out_clauses                       false
% 2.78/0.96  
% 2.78/0.96  ------ QBF Options
% 2.78/0.96  
% 2.78/0.96  --qbf_mode                              false
% 2.78/0.96  --qbf_elim_univ                         false
% 2.78/0.96  --qbf_dom_inst                          none
% 2.78/0.96  --qbf_dom_pre_inst                      false
% 2.78/0.96  --qbf_sk_in                             false
% 2.78/0.96  --qbf_pred_elim                         true
% 2.78/0.96  --qbf_split                             512
% 2.78/0.96  
% 2.78/0.96  ------ BMC1 Options
% 2.78/0.96  
% 2.78/0.96  --bmc1_incremental                      false
% 2.78/0.96  --bmc1_axioms                           reachable_all
% 2.78/0.96  --bmc1_min_bound                        0
% 2.78/0.96  --bmc1_max_bound                        -1
% 2.78/0.96  --bmc1_max_bound_default                -1
% 2.78/0.96  --bmc1_symbol_reachability              true
% 2.78/0.96  --bmc1_property_lemmas                  false
% 2.78/0.96  --bmc1_k_induction                      false
% 2.78/0.96  --bmc1_non_equiv_states                 false
% 2.78/0.96  --bmc1_deadlock                         false
% 2.78/0.96  --bmc1_ucm                              false
% 2.78/0.96  --bmc1_add_unsat_core                   none
% 2.78/0.96  --bmc1_unsat_core_children              false
% 2.78/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.96  --bmc1_out_stat                         full
% 2.78/0.96  --bmc1_ground_init                      false
% 2.78/0.96  --bmc1_pre_inst_next_state              false
% 2.78/0.96  --bmc1_pre_inst_state                   false
% 2.78/0.96  --bmc1_pre_inst_reach_state             false
% 2.78/0.96  --bmc1_out_unsat_core                   false
% 2.78/0.96  --bmc1_aig_witness_out                  false
% 2.78/0.96  --bmc1_verbose                          false
% 2.78/0.96  --bmc1_dump_clauses_tptp                false
% 2.78/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.96  --bmc1_dump_file                        -
% 2.78/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.96  --bmc1_ucm_extend_mode                  1
% 2.78/0.96  --bmc1_ucm_init_mode                    2
% 2.78/0.96  --bmc1_ucm_cone_mode                    none
% 2.78/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.96  --bmc1_ucm_relax_model                  4
% 2.78/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.96  --bmc1_ucm_layered_model                none
% 2.78/0.96  --bmc1_ucm_max_lemma_size               10
% 2.78/0.96  
% 2.78/0.96  ------ AIG Options
% 2.78/0.96  
% 2.78/0.96  --aig_mode                              false
% 2.78/0.96  
% 2.78/0.96  ------ Instantiation Options
% 2.78/0.96  
% 2.78/0.96  --instantiation_flag                    true
% 2.78/0.96  --inst_sos_flag                         false
% 2.78/0.96  --inst_sos_phase                        true
% 2.78/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.96  --inst_lit_sel_side                     num_symb
% 2.78/0.96  --inst_solver_per_active                1400
% 2.78/0.96  --inst_solver_calls_frac                1.
% 2.78/0.96  --inst_passive_queue_type               priority_queues
% 2.78/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.96  --inst_passive_queues_freq              [25;2]
% 2.78/0.96  --inst_dismatching                      true
% 2.78/0.96  --inst_eager_unprocessed_to_passive     true
% 2.78/0.96  --inst_prop_sim_given                   true
% 2.78/0.96  --inst_prop_sim_new                     false
% 2.78/0.96  --inst_subs_new                         false
% 2.78/0.96  --inst_eq_res_simp                      false
% 2.78/0.96  --inst_subs_given                       false
% 2.78/0.96  --inst_orphan_elimination               true
% 2.78/0.96  --inst_learning_loop_flag               true
% 2.78/0.96  --inst_learning_start                   3000
% 2.78/0.96  --inst_learning_factor                  2
% 2.78/0.96  --inst_start_prop_sim_after_learn       3
% 2.78/0.96  --inst_sel_renew                        solver
% 2.78/0.96  --inst_lit_activity_flag                true
% 2.78/0.96  --inst_restr_to_given                   false
% 2.78/0.96  --inst_activity_threshold               500
% 2.78/0.96  --inst_out_proof                        true
% 2.78/0.96  
% 2.78/0.96  ------ Resolution Options
% 2.78/0.96  
% 2.78/0.96  --resolution_flag                       true
% 2.78/0.96  --res_lit_sel                           adaptive
% 2.78/0.96  --res_lit_sel_side                      none
% 2.78/0.96  --res_ordering                          kbo
% 2.78/0.96  --res_to_prop_solver                    active
% 2.78/0.96  --res_prop_simpl_new                    false
% 2.78/0.96  --res_prop_simpl_given                  true
% 2.78/0.96  --res_passive_queue_type                priority_queues
% 2.78/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.96  --res_passive_queues_freq               [15;5]
% 2.78/0.96  --res_forward_subs                      full
% 2.78/0.96  --res_backward_subs                     full
% 2.78/0.96  --res_forward_subs_resolution           true
% 2.78/0.96  --res_backward_subs_resolution          true
% 2.78/0.96  --res_orphan_elimination                true
% 2.78/0.96  --res_time_limit                        2.
% 2.78/0.96  --res_out_proof                         true
% 2.78/0.96  
% 2.78/0.96  ------ Superposition Options
% 2.78/0.96  
% 2.78/0.96  --superposition_flag                    true
% 2.78/0.96  --sup_passive_queue_type                priority_queues
% 2.78/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.96  --demod_completeness_check              fast
% 2.78/0.96  --demod_use_ground                      true
% 2.78/0.96  --sup_to_prop_solver                    passive
% 2.78/0.96  --sup_prop_simpl_new                    true
% 2.78/0.96  --sup_prop_simpl_given                  true
% 2.78/0.96  --sup_fun_splitting                     false
% 2.78/0.96  --sup_smt_interval                      50000
% 2.78/0.96  
% 2.78/0.96  ------ Superposition Simplification Setup
% 2.78/0.96  
% 2.78/0.96  --sup_indices_passive                   []
% 2.78/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.96  --sup_full_bw                           [BwDemod]
% 2.78/0.96  --sup_immed_triv                        [TrivRules]
% 2.78/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.96  --sup_immed_bw_main                     []
% 2.78/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.96  
% 2.78/0.96  ------ Combination Options
% 2.78/0.96  
% 2.78/0.96  --comb_res_mult                         3
% 2.78/0.96  --comb_sup_mult                         2
% 2.78/0.96  --comb_inst_mult                        10
% 2.78/0.96  
% 2.78/0.96  ------ Debug Options
% 2.78/0.96  
% 2.78/0.96  --dbg_backtrace                         false
% 2.78/0.96  --dbg_dump_prop_clauses                 false
% 2.78/0.96  --dbg_dump_prop_clauses_file            -
% 2.78/0.96  --dbg_out_stat                          false
% 2.78/0.96  ------ Parsing...
% 2.78/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.96  
% 2.78/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.78/0.96  
% 2.78/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.96  
% 2.78/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.96  ------ Proving...
% 2.78/0.96  ------ Problem Properties 
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  clauses                                 44
% 2.78/0.96  conjectures                             17
% 2.78/0.96  EPR                                     17
% 2.78/0.96  Horn                                    36
% 2.78/0.96  unary                                   17
% 2.78/0.96  binary                                  7
% 2.78/0.96  lits                                    136
% 2.78/0.96  lits eq                                 11
% 2.78/0.96  fd_pure                                 0
% 2.78/0.96  fd_pseudo                               0
% 2.78/0.96  fd_cond                                 0
% 2.78/0.96  fd_pseudo_cond                          2
% 2.78/0.96  AC symbols                              0
% 2.78/0.96  
% 2.78/0.96  ------ Schedule dynamic 5 is on 
% 2.78/0.96  
% 2.78/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  ------ 
% 2.78/0.96  Current options:
% 2.78/0.96  ------ 
% 2.78/0.96  
% 2.78/0.96  ------ Input Options
% 2.78/0.96  
% 2.78/0.96  --out_options                           all
% 2.78/0.96  --tptp_safe_out                         true
% 2.78/0.96  --problem_path                          ""
% 2.78/0.96  --include_path                          ""
% 2.78/0.96  --clausifier                            res/vclausify_rel
% 2.78/0.96  --clausifier_options                    --mode clausify
% 2.78/0.96  --stdin                                 false
% 2.78/0.96  --stats_out                             all
% 2.78/0.96  
% 2.78/0.96  ------ General Options
% 2.78/0.96  
% 2.78/0.96  --fof                                   false
% 2.78/0.96  --time_out_real                         305.
% 2.78/0.96  --time_out_virtual                      -1.
% 2.78/0.96  --symbol_type_check                     false
% 2.78/0.96  --clausify_out                          false
% 2.78/0.96  --sig_cnt_out                           false
% 2.78/0.96  --trig_cnt_out                          false
% 2.78/0.96  --trig_cnt_out_tolerance                1.
% 2.78/0.96  --trig_cnt_out_sk_spl                   false
% 2.78/0.96  --abstr_cl_out                          false
% 2.78/0.96  
% 2.78/0.96  ------ Global Options
% 2.78/0.96  
% 2.78/0.96  --schedule                              default
% 2.78/0.96  --add_important_lit                     false
% 2.78/0.96  --prop_solver_per_cl                    1000
% 2.78/0.96  --min_unsat_core                        false
% 2.78/0.96  --soft_assumptions                      false
% 2.78/0.96  --soft_lemma_size                       3
% 2.78/0.96  --prop_impl_unit_size                   0
% 2.78/0.96  --prop_impl_unit                        []
% 2.78/0.96  --share_sel_clauses                     true
% 2.78/0.96  --reset_solvers                         false
% 2.78/0.96  --bc_imp_inh                            [conj_cone]
% 2.78/0.96  --conj_cone_tolerance                   3.
% 2.78/0.96  --extra_neg_conj                        none
% 2.78/0.96  --large_theory_mode                     true
% 2.78/0.96  --prolific_symb_bound                   200
% 2.78/0.96  --lt_threshold                          2000
% 2.78/0.96  --clause_weak_htbl                      true
% 2.78/0.96  --gc_record_bc_elim                     false
% 2.78/0.96  
% 2.78/0.96  ------ Preprocessing Options
% 2.78/0.96  
% 2.78/0.96  --preprocessing_flag                    true
% 2.78/0.96  --time_out_prep_mult                    0.1
% 2.78/0.96  --splitting_mode                        input
% 2.78/0.96  --splitting_grd                         true
% 2.78/0.96  --splitting_cvd                         false
% 2.78/0.96  --splitting_cvd_svl                     false
% 2.78/0.96  --splitting_nvd                         32
% 2.78/0.96  --sub_typing                            true
% 2.78/0.96  --prep_gs_sim                           true
% 2.78/0.96  --prep_unflatten                        true
% 2.78/0.96  --prep_res_sim                          true
% 2.78/0.96  --prep_upred                            true
% 2.78/0.96  --prep_sem_filter                       exhaustive
% 2.78/0.96  --prep_sem_filter_out                   false
% 2.78/0.96  --pred_elim                             true
% 2.78/0.96  --res_sim_input                         true
% 2.78/0.96  --eq_ax_congr_red                       true
% 2.78/0.96  --pure_diseq_elim                       true
% 2.78/0.96  --brand_transform                       false
% 2.78/0.96  --non_eq_to_eq                          false
% 2.78/0.96  --prep_def_merge                        true
% 2.78/0.96  --prep_def_merge_prop_impl              false
% 2.78/0.96  --prep_def_merge_mbd                    true
% 2.78/0.96  --prep_def_merge_tr_red                 false
% 2.78/0.96  --prep_def_merge_tr_cl                  false
% 2.78/0.96  --smt_preprocessing                     true
% 2.78/0.96  --smt_ac_axioms                         fast
% 2.78/0.96  --preprocessed_out                      false
% 2.78/0.96  --preprocessed_stats                    false
% 2.78/0.96  
% 2.78/0.96  ------ Abstraction refinement Options
% 2.78/0.96  
% 2.78/0.96  --abstr_ref                             []
% 2.78/0.96  --abstr_ref_prep                        false
% 2.78/0.96  --abstr_ref_until_sat                   false
% 2.78/0.96  --abstr_ref_sig_restrict                funpre
% 2.78/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.96  --abstr_ref_under                       []
% 2.78/0.96  
% 2.78/0.96  ------ SAT Options
% 2.78/0.96  
% 2.78/0.96  --sat_mode                              false
% 2.78/0.96  --sat_fm_restart_options                ""
% 2.78/0.96  --sat_gr_def                            false
% 2.78/0.96  --sat_epr_types                         true
% 2.78/0.96  --sat_non_cyclic_types                  false
% 2.78/0.96  --sat_finite_models                     false
% 2.78/0.96  --sat_fm_lemmas                         false
% 2.78/0.96  --sat_fm_prep                           false
% 2.78/0.96  --sat_fm_uc_incr                        true
% 2.78/0.96  --sat_out_model                         small
% 2.78/0.96  --sat_out_clauses                       false
% 2.78/0.96  
% 2.78/0.96  ------ QBF Options
% 2.78/0.96  
% 2.78/0.96  --qbf_mode                              false
% 2.78/0.96  --qbf_elim_univ                         false
% 2.78/0.96  --qbf_dom_inst                          none
% 2.78/0.96  --qbf_dom_pre_inst                      false
% 2.78/0.96  --qbf_sk_in                             false
% 2.78/0.96  --qbf_pred_elim                         true
% 2.78/0.96  --qbf_split                             512
% 2.78/0.96  
% 2.78/0.96  ------ BMC1 Options
% 2.78/0.96  
% 2.78/0.96  --bmc1_incremental                      false
% 2.78/0.96  --bmc1_axioms                           reachable_all
% 2.78/0.96  --bmc1_min_bound                        0
% 2.78/0.96  --bmc1_max_bound                        -1
% 2.78/0.96  --bmc1_max_bound_default                -1
% 2.78/0.96  --bmc1_symbol_reachability              true
% 2.78/0.96  --bmc1_property_lemmas                  false
% 2.78/0.96  --bmc1_k_induction                      false
% 2.78/0.96  --bmc1_non_equiv_states                 false
% 2.78/0.96  --bmc1_deadlock                         false
% 2.78/0.96  --bmc1_ucm                              false
% 2.78/0.96  --bmc1_add_unsat_core                   none
% 2.78/0.96  --bmc1_unsat_core_children              false
% 2.78/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.96  --bmc1_out_stat                         full
% 2.78/0.96  --bmc1_ground_init                      false
% 2.78/0.96  --bmc1_pre_inst_next_state              false
% 2.78/0.96  --bmc1_pre_inst_state                   false
% 2.78/0.96  --bmc1_pre_inst_reach_state             false
% 2.78/0.96  --bmc1_out_unsat_core                   false
% 2.78/0.96  --bmc1_aig_witness_out                  false
% 2.78/0.96  --bmc1_verbose                          false
% 2.78/0.96  --bmc1_dump_clauses_tptp                false
% 2.78/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.96  --bmc1_dump_file                        -
% 2.78/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.96  --bmc1_ucm_extend_mode                  1
% 2.78/0.96  --bmc1_ucm_init_mode                    2
% 2.78/0.96  --bmc1_ucm_cone_mode                    none
% 2.78/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.96  --bmc1_ucm_relax_model                  4
% 2.78/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.96  --bmc1_ucm_layered_model                none
% 2.78/0.96  --bmc1_ucm_max_lemma_size               10
% 2.78/0.96  
% 2.78/0.96  ------ AIG Options
% 2.78/0.96  
% 2.78/0.96  --aig_mode                              false
% 2.78/0.96  
% 2.78/0.96  ------ Instantiation Options
% 2.78/0.96  
% 2.78/0.96  --instantiation_flag                    true
% 2.78/0.96  --inst_sos_flag                         false
% 2.78/0.96  --inst_sos_phase                        true
% 2.78/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.96  --inst_lit_sel_side                     none
% 2.78/0.96  --inst_solver_per_active                1400
% 2.78/0.96  --inst_solver_calls_frac                1.
% 2.78/0.96  --inst_passive_queue_type               priority_queues
% 2.78/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.96  --inst_passive_queues_freq              [25;2]
% 2.78/0.96  --inst_dismatching                      true
% 2.78/0.96  --inst_eager_unprocessed_to_passive     true
% 2.78/0.96  --inst_prop_sim_given                   true
% 2.78/0.96  --inst_prop_sim_new                     false
% 2.78/0.96  --inst_subs_new                         false
% 2.78/0.96  --inst_eq_res_simp                      false
% 2.78/0.96  --inst_subs_given                       false
% 2.78/0.96  --inst_orphan_elimination               true
% 2.78/0.96  --inst_learning_loop_flag               true
% 2.78/0.96  --inst_learning_start                   3000
% 2.78/0.96  --inst_learning_factor                  2
% 2.78/0.96  --inst_start_prop_sim_after_learn       3
% 2.78/0.96  --inst_sel_renew                        solver
% 2.78/0.96  --inst_lit_activity_flag                true
% 2.78/0.96  --inst_restr_to_given                   false
% 2.78/0.96  --inst_activity_threshold               500
% 2.78/0.96  --inst_out_proof                        true
% 2.78/0.96  
% 2.78/0.96  ------ Resolution Options
% 2.78/0.96  
% 2.78/0.96  --resolution_flag                       false
% 2.78/0.96  --res_lit_sel                           adaptive
% 2.78/0.96  --res_lit_sel_side                      none
% 2.78/0.96  --res_ordering                          kbo
% 2.78/0.96  --res_to_prop_solver                    active
% 2.78/0.96  --res_prop_simpl_new                    false
% 2.78/0.96  --res_prop_simpl_given                  true
% 2.78/0.96  --res_passive_queue_type                priority_queues
% 2.78/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.96  --res_passive_queues_freq               [15;5]
% 2.78/0.96  --res_forward_subs                      full
% 2.78/0.96  --res_backward_subs                     full
% 2.78/0.96  --res_forward_subs_resolution           true
% 2.78/0.96  --res_backward_subs_resolution          true
% 2.78/0.96  --res_orphan_elimination                true
% 2.78/0.96  --res_time_limit                        2.
% 2.78/0.96  --res_out_proof                         true
% 2.78/0.96  
% 2.78/0.96  ------ Superposition Options
% 2.78/0.96  
% 2.78/0.96  --superposition_flag                    true
% 2.78/0.96  --sup_passive_queue_type                priority_queues
% 2.78/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.96  --demod_completeness_check              fast
% 2.78/0.96  --demod_use_ground                      true
% 2.78/0.96  --sup_to_prop_solver                    passive
% 2.78/0.96  --sup_prop_simpl_new                    true
% 2.78/0.96  --sup_prop_simpl_given                  true
% 2.78/0.96  --sup_fun_splitting                     false
% 2.78/0.96  --sup_smt_interval                      50000
% 2.78/0.96  
% 2.78/0.96  ------ Superposition Simplification Setup
% 2.78/0.96  
% 2.78/0.96  --sup_indices_passive                   []
% 2.78/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.96  --sup_full_bw                           [BwDemod]
% 2.78/0.96  --sup_immed_triv                        [TrivRules]
% 2.78/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.96  --sup_immed_bw_main                     []
% 2.78/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.96  
% 2.78/0.96  ------ Combination Options
% 2.78/0.96  
% 2.78/0.96  --comb_res_mult                         3
% 2.78/0.96  --comb_sup_mult                         2
% 2.78/0.96  --comb_inst_mult                        10
% 2.78/0.96  
% 2.78/0.96  ------ Debug Options
% 2.78/0.96  
% 2.78/0.96  --dbg_backtrace                         false
% 2.78/0.96  --dbg_dump_prop_clauses                 false
% 2.78/0.96  --dbg_dump_prop_clauses_file            -
% 2.78/0.96  --dbg_out_stat                          false
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  ------ Proving...
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  % SZS status Theorem for theBenchmark.p
% 2.78/0.96  
% 2.78/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.96  
% 2.78/0.96  fof(f15,conjecture,(
% 2.78/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f16,negated_conjecture,(
% 2.78/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.78/0.96    inference(negated_conjecture,[],[f15])).
% 2.78/0.96  
% 2.78/0.96  fof(f39,plain,(
% 2.78/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.78/0.96    inference(ennf_transformation,[],[f16])).
% 2.78/0.96  
% 2.78/0.96  fof(f40,plain,(
% 2.78/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.78/0.96    inference(flattening,[],[f39])).
% 2.78/0.96  
% 2.78/0.96  fof(f64,plain,(
% 2.78/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f63,plain,(
% 2.78/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f62,plain,(
% 2.78/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f61,plain,(
% 2.78/0.96    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f60,plain,(
% 2.78/0.96    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f59,plain,(
% 2.78/0.96    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f58,plain,(
% 2.78/0.96    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f65,plain,(
% 2.78/0.96    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.78/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f40,f64,f63,f62,f61,f60,f59,f58])).
% 2.78/0.96  
% 2.78/0.96  fof(f105,plain,(
% 2.78/0.96    m1_pre_topc(sK6,sK4)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f2,axiom,(
% 2.78/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f20,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.96    inference(ennf_transformation,[],[f2])).
% 2.78/0.96  
% 2.78/0.96  fof(f21,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f20])).
% 2.78/0.96  
% 2.78/0.96  fof(f67,plain,(
% 2.78/0.96    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f21])).
% 2.78/0.96  
% 2.78/0.96  fof(f99,plain,(
% 2.78/0.96    v2_pre_topc(sK4)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f100,plain,(
% 2.78/0.96    l1_pre_topc(sK4)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f111,plain,(
% 2.78/0.96    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f7,axiom,(
% 2.78/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f27,plain,(
% 2.78/0.96    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.96    inference(ennf_transformation,[],[f7])).
% 2.78/0.96  
% 2.78/0.96  fof(f28,plain,(
% 2.78/0.96    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f27])).
% 2.78/0.96  
% 2.78/0.96  fof(f84,plain,(
% 2.78/0.96    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f28])).
% 2.78/0.96  
% 2.78/0.96  fof(f5,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f25,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f5])).
% 2.78/0.96  
% 2.78/0.96  fof(f82,plain,(
% 2.78/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f25])).
% 2.78/0.96  
% 2.78/0.96  fof(f107,plain,(
% 2.78/0.96    m1_pre_topc(sK7,sK4)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f1,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f18,plain,(
% 2.78/0.96    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f1])).
% 2.78/0.96  
% 2.78/0.96  fof(f19,plain,(
% 2.78/0.96    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f18])).
% 2.78/0.96  
% 2.78/0.96  fof(f66,plain,(
% 2.78/0.96    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f19])).
% 2.78/0.96  
% 2.78/0.96  fof(f8,axiom,(
% 2.78/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f29,plain,(
% 2.78/0.96    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/0.96    inference(ennf_transformation,[],[f8])).
% 2.78/0.96  
% 2.78/0.96  fof(f87,plain,(
% 2.78/0.96    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/0.96    inference(cnf_transformation,[],[f29])).
% 2.78/0.96  
% 2.78/0.96  fof(f6,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f26,plain,(
% 2.78/0.96    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f6])).
% 2.78/0.96  
% 2.78/0.96  fof(f83,plain,(
% 2.78/0.96    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f26])).
% 2.78/0.96  
% 2.78/0.96  fof(f3,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f17,plain,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.78/0.96    inference(rectify,[],[f3])).
% 2.78/0.96  
% 2.78/0.96  fof(f22,plain,(
% 2.78/0.96    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f17])).
% 2.78/0.96  
% 2.78/0.96  fof(f23,plain,(
% 2.78/0.96    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f22])).
% 2.78/0.96  
% 2.78/0.96  fof(f41,plain,(
% 2.78/0.96    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.78/0.96    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.78/0.96  
% 2.78/0.96  fof(f42,plain,(
% 2.78/0.96    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(definition_folding,[],[f23,f41])).
% 2.78/0.96  
% 2.78/0.96  fof(f48,plain,(
% 2.78/0.96    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(nnf_transformation,[],[f42])).
% 2.78/0.96  
% 2.78/0.96  fof(f49,plain,(
% 2.78/0.96    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f48])).
% 2.78/0.96  
% 2.78/0.96  fof(f50,plain,(
% 2.78/0.96    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(rectify,[],[f49])).
% 2.78/0.96  
% 2.78/0.96  fof(f51,plain,(
% 2.78/0.96    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.78/0.96    introduced(choice_axiom,[])).
% 2.78/0.96  
% 2.78/0.96  fof(f52,plain,(
% 2.78/0.96    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 2.78/0.96  
% 2.78/0.96  fof(f74,plain,(
% 2.78/0.96    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f52])).
% 2.78/0.96  
% 2.78/0.96  fof(f115,plain,(
% 2.78/0.96    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f114,plain,(
% 2.78/0.96    sK9 = sK10),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f4,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f24,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f4])).
% 2.78/0.96  
% 2.78/0.96  fof(f53,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(nnf_transformation,[],[f24])).
% 2.78/0.96  
% 2.78/0.96  fof(f81,plain,(
% 2.78/0.96    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f53])).
% 2.78/0.96  
% 2.78/0.96  fof(f10,axiom,(
% 2.78/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f31,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.96    inference(ennf_transformation,[],[f10])).
% 2.78/0.96  
% 2.78/0.96  fof(f32,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f31])).
% 2.78/0.96  
% 2.78/0.96  fof(f55,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.96    inference(nnf_transformation,[],[f32])).
% 2.78/0.96  
% 2.78/0.96  fof(f56,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f55])).
% 2.78/0.96  
% 2.78/0.96  fof(f91,plain,(
% 2.78/0.96    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f56])).
% 2.78/0.96  
% 2.78/0.96  fof(f118,plain,(
% 2.78/0.96    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.96    inference(equality_resolution,[],[f91])).
% 2.78/0.96  
% 2.78/0.96  fof(f11,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f33,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f11])).
% 2.78/0.96  
% 2.78/0.96  fof(f93,plain,(
% 2.78/0.96    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f33])).
% 2.78/0.96  
% 2.78/0.96  fof(f14,axiom,(
% 2.78/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f37,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.78/0.96    inference(ennf_transformation,[],[f14])).
% 2.78/0.96  
% 2.78/0.96  fof(f38,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/0.96    inference(flattening,[],[f37])).
% 2.78/0.96  
% 2.78/0.96  fof(f57,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/0.96    inference(nnf_transformation,[],[f38])).
% 2.78/0.96  
% 2.78/0.96  fof(f97,plain,(
% 2.78/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f57])).
% 2.78/0.96  
% 2.78/0.96  fof(f120,plain,(
% 2.78/0.96    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.78/0.96    inference(equality_resolution,[],[f97])).
% 2.78/0.96  
% 2.78/0.96  fof(f109,plain,(
% 2.78/0.96    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f108,plain,(
% 2.78/0.96    v1_funct_1(sK8)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f13,axiom,(
% 2.78/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f35,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/0.96    inference(ennf_transformation,[],[f13])).
% 2.78/0.96  
% 2.78/0.96  fof(f36,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/0.96    inference(flattening,[],[f35])).
% 2.78/0.96  
% 2.78/0.96  fof(f95,plain,(
% 2.78/0.96    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f36])).
% 2.78/0.96  
% 2.78/0.96  fof(f101,plain,(
% 2.78/0.96    ~v2_struct_0(sK5)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f102,plain,(
% 2.78/0.96    v2_pre_topc(sK5)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f103,plain,(
% 2.78/0.96    l1_pre_topc(sK5)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f106,plain,(
% 2.78/0.96    ~v2_struct_0(sK7)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f110,plain,(
% 2.78/0.96    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f98,plain,(
% 2.78/0.96    ~v2_struct_0(sK4)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f104,plain,(
% 2.78/0.96    ~v2_struct_0(sK6)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f112,plain,(
% 2.78/0.96    m1_subset_1(sK9,u1_struct_0(sK7))),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f116,plain,(
% 2.78/0.96    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f113,plain,(
% 2.78/0.96    m1_subset_1(sK10,u1_struct_0(sK6))),
% 2.78/0.96    inference(cnf_transformation,[],[f65])).
% 2.78/0.96  
% 2.78/0.96  fof(f12,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f34,plain,(
% 2.78/0.96    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f12])).
% 2.78/0.96  
% 2.78/0.96  fof(f94,plain,(
% 2.78/0.96    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f34])).
% 2.78/0.96  
% 2.78/0.96  fof(f9,axiom,(
% 2.78/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.78/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.96  
% 2.78/0.96  fof(f30,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(ennf_transformation,[],[f9])).
% 2.78/0.96  
% 2.78/0.96  fof(f54,plain,(
% 2.78/0.96    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.78/0.96    inference(nnf_transformation,[],[f30])).
% 2.78/0.96  
% 2.78/0.96  fof(f88,plain,(
% 2.78/0.96    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.78/0.96    inference(cnf_transformation,[],[f54])).
% 2.78/0.96  
% 2.78/0.96  cnf(c_43,negated_conjecture,
% 2.78/0.96      ( m1_pre_topc(sK6,sK4) ),
% 2.78/0.96      inference(cnf_transformation,[],[f105]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3092,plain,
% 2.78/0.96      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_1,plain,
% 2.78/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | v2_pre_topc(X0)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f67]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3122,plain,
% 2.78/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.78/0.96      | v2_pre_topc(X1) != iProver_top
% 2.78/0.96      | v2_pre_topc(X0) = iProver_top
% 2.78/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6509,plain,
% 2.78/0.96      ( v2_pre_topc(sK4) != iProver_top
% 2.78/0.96      | v2_pre_topc(sK6) = iProver_top
% 2.78/0.96      | l1_pre_topc(sK4) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_3092,c_3122]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_49,negated_conjecture,
% 2.78/0.96      ( v2_pre_topc(sK4) ),
% 2.78/0.96      inference(cnf_transformation,[],[f99]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_52,plain,
% 2.78/0.96      ( v2_pre_topc(sK4) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_48,negated_conjecture,
% 2.78/0.96      ( l1_pre_topc(sK4) ),
% 2.78/0.96      inference(cnf_transformation,[],[f100]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_53,plain,
% 2.78/0.96      ( l1_pre_topc(sK4) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6541,plain,
% 2.78/0.96      ( v2_pre_topc(sK6) = iProver_top ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_6509,c_52,c_53]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_37,negated_conjecture,
% 2.78/0.96      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 2.78/0.96      inference(cnf_transformation,[],[f111]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_19,plain,
% 2.78/0.96      ( ~ v2_pre_topc(X0)
% 2.78/0.96      | ~ l1_pre_topc(X0)
% 2.78/0.96      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.78/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3106,plain,
% 2.78/0.96      ( v2_pre_topc(X0) != iProver_top
% 2.78/0.96      | l1_pre_topc(X0) != iProver_top
% 2.78/0.96      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_5502,plain,
% 2.78/0.96      ( v2_pre_topc(sK6) != iProver_top
% 2.78/0.96      | l1_pre_topc(sK6) != iProver_top
% 2.78/0.96      | v1_pre_topc(sK7) = iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_37,c_3106]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_16,plain,
% 2.78/0.96      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.78/0.96      inference(cnf_transformation,[],[f82]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3109,plain,
% 2.78/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.78/0.96      | l1_pre_topc(X1) != iProver_top
% 2.78/0.96      | l1_pre_topc(X0) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4962,plain,
% 2.78/0.96      ( l1_pre_topc(sK4) != iProver_top
% 2.78/0.96      | l1_pre_topc(sK6) = iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_3092,c_3109]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_5608,plain,
% 2.78/0.96      ( v2_pre_topc(sK6) != iProver_top
% 2.78/0.96      | v1_pre_topc(sK7) = iProver_top ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_5502,c_53,c_4962]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6546,plain,
% 2.78/0.96      ( v1_pre_topc(sK7) = iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_6541,c_5608]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_41,negated_conjecture,
% 2.78/0.96      ( m1_pre_topc(sK7,sK4) ),
% 2.78/0.96      inference(cnf_transformation,[],[f107]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3094,plain,
% 2.78/0.96      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4961,plain,
% 2.78/0.96      ( l1_pre_topc(sK4) != iProver_top
% 2.78/0.96      | l1_pre_topc(sK7) = iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_3094,c_3109]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_5101,plain,
% 2.78/0.96      ( l1_pre_topc(sK7) = iProver_top ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_4961,c_53]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_0,plain,
% 2.78/0.96      ( ~ l1_pre_topc(X0)
% 2.78/0.96      | ~ v1_pre_topc(X0)
% 2.78/0.96      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.78/0.96      inference(cnf_transformation,[],[f66]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3123,plain,
% 2.78/0.96      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.78/0.96      | l1_pre_topc(X0) != iProver_top
% 2.78/0.96      | v1_pre_topc(X0) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_5383,plain,
% 2.78/0.96      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
% 2.78/0.96      | v1_pre_topc(sK7) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_5101,c_3123]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6614,plain,
% 2.78/0.96      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_6546,c_5383]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_20,plain,
% 2.78/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.78/0.96      | X2 = X0
% 2.78/0.96      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 2.78/0.96      inference(cnf_transformation,[],[f87]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3105,plain,
% 2.78/0.96      ( X0 = X1
% 2.78/0.96      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 2.78/0.96      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6122,plain,
% 2.78/0.96      ( g1_pre_topc(X0,X1) != sK7
% 2.78/0.96      | u1_pre_topc(sK6) = X1
% 2.78/0.96      | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_37,c_3105]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6821,plain,
% 2.78/0.96      ( u1_pre_topc(sK7) = u1_pre_topc(sK6)
% 2.78/0.96      | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_6614,c_6122]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_17,plain,
% 2.78/0.96      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.78/0.96      | ~ l1_pre_topc(X0) ),
% 2.78/0.96      inference(cnf_transformation,[],[f83]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3716,plain,
% 2.78/0.96      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 2.78/0.96      | ~ l1_pre_topc(sK7) ),
% 2.78/0.96      inference(instantiation,[status(thm)],[c_17]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3721,plain,
% 2.78/0.96      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
% 2.78/0.96      | l1_pre_topc(sK7) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_3716]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6121,plain,
% 2.78/0.96      ( g1_pre_topc(X0,X1) != sK7
% 2.78/0.96      | u1_pre_topc(sK6) = X1
% 2.78/0.96      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_37,c_3105]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_6823,plain,
% 2.78/0.96      ( u1_pre_topc(sK7) = u1_pre_topc(sK6)
% 2.78/0.96      | m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_6614,c_6121]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_7086,plain,
% 2.78/0.96      ( u1_pre_topc(sK7) = u1_pre_topc(sK6) ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_6821,c_53,c_3721,c_4961,c_6823]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_13,plain,
% 2.78/0.96      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.78/0.96      | ~ v2_pre_topc(X0)
% 2.78/0.96      | ~ l1_pre_topc(X0) ),
% 2.78/0.96      inference(cnf_transformation,[],[f74]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3110,plain,
% 2.78/0.96      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 2.78/0.96      | v2_pre_topc(X0) != iProver_top
% 2.78/0.96      | l1_pre_topc(X0) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_7117,plain,
% 2.78/0.96      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) = iProver_top
% 2.78/0.96      | v2_pre_topc(sK6) != iProver_top
% 2.78/0.96      | l1_pre_topc(sK6) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_7086,c_3110]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_33,negated_conjecture,
% 2.78/0.96      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 2.78/0.96      inference(cnf_transformation,[],[f115]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3098,plain,
% 2.78/0.96      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_34,negated_conjecture,
% 2.78/0.96      ( sK9 = sK10 ),
% 2.78/0.96      inference(cnf_transformation,[],[f114]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3161,plain,
% 2.78/0.96      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 2.78/0.96      inference(light_normalisation,[status(thm)],[c_3098,c_34]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_14,plain,
% 2.78/0.96      ( v3_pre_topc(X0,X1)
% 2.78/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.96      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f81]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_25,plain,
% 2.78/0.96      ( v1_tsep_1(X0,X1)
% 2.78/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.78/0.96      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f118]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_27,plain,
% 2.78/0.96      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f93]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_274,plain,
% 2.78/0.96      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.78/0.96      | v1_tsep_1(X0,X1)
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_25,c_27]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_275,plain,
% 2.78/0.96      ( v1_tsep_1(X0,X1)
% 2.78/0.96      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(renaming,[status(thm)],[c_274]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_594,plain,
% 2.78/0.96      ( v1_tsep_1(X0,X1)
% 2.78/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.78/0.96      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X3)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | X1 != X3
% 2.78/0.96      | u1_struct_0(X0) != X2 ),
% 2.78/0.96      inference(resolution_lifted,[status(thm)],[c_14,c_275]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_595,plain,
% 2.78/0.96      ( v1_tsep_1(X0,X1)
% 2.78/0.96      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.96      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(unflattening,[status(thm)],[c_594]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_599,plain,
% 2.78/0.96      ( v1_tsep_1(X0,X1)
% 2.78/0.96      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_595,c_27]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_30,plain,
% 2.78/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 2.78/0.96      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.78/0.96      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.78/0.96      | ~ v1_tsep_1(X4,X0)
% 2.78/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.78/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.78/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_pre_topc(X0,X5)
% 2.78/0.96      | ~ m1_pre_topc(X4,X0)
% 2.78/0.96      | ~ m1_pre_topc(X4,X5)
% 2.78/0.96      | v2_struct_0(X5)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X4)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | ~ v1_funct_1(X2)
% 2.78/0.96      | ~ v2_pre_topc(X5)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X5)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f120]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_39,negated_conjecture,
% 2.78/0.96      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 2.78/0.96      inference(cnf_transformation,[],[f109]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_729,plain,
% 2.78/0.96      ( r1_tmap_1(X0,X1,X2,X3)
% 2.78/0.96      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.78/0.96      | ~ v1_tsep_1(X4,X0)
% 2.78/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.78/0.96      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.78/0.96      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_pre_topc(X4,X0)
% 2.78/0.96      | ~ m1_pre_topc(X0,X5)
% 2.78/0.96      | ~ m1_pre_topc(X4,X5)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X4)
% 2.78/0.96      | v2_struct_0(X5)
% 2.78/0.96      | ~ v1_funct_1(X2)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X5)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X5)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X0) != u1_struct_0(sK7)
% 2.78/0.96      | sK8 != X2 ),
% 2.78/0.96      inference(resolution_lifted,[status(thm)],[c_30,c_39]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_730,plain,
% 2.78/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ v1_tsep_1(X0,X3)
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | ~ m1_pre_topc(X0,X2)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X2)
% 2.78/0.96      | ~ v1_funct_1(sK8)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(unflattening,[status(thm)],[c_729]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_40,negated_conjecture,
% 2.78/0.96      ( v1_funct_1(sK8) ),
% 2.78/0.96      inference(cnf_transformation,[],[f108]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_734,plain,
% 2.78/0.96      ( v2_struct_0(X2)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | ~ m1_pre_topc(X0,X2)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ v1_tsep_1(X0,X3)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_730,c_40]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_735,plain,
% 2.78/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ v1_tsep_1(X0,X3)
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | ~ m1_pre_topc(X0,X2)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X2)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(renaming,[status(thm)],[c_734]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_29,plain,
% 2.78/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ m1_pre_topc(X2,X0)
% 2.78/0.96      | m1_pre_topc(X2,X1)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f95]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_778,plain,
% 2.78/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ v1_tsep_1(X0,X3)
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X2)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(forward_subsumption_resolution,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_735,c_29]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_801,plain,
% 2.78/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
% 2.78/0.96      | ~ m1_pre_topc(X5,X6)
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X2)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | ~ v2_pre_topc(X6)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X6)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | X0 != X5
% 2.78/0.96      | X3 != X6
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(resolution_lifted,[status(thm)],[c_599,c_778]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_802,plain,
% 2.78/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X2)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ v2_pre_topc(X3)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X3)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(unflattening,[status(thm)],[c_801]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_846,plain,
% 2.78/0.96      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK8),X4)
% 2.78/0.96      | r1_tmap_1(X3,X1,sK8,X4)
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.78/0.96      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.78/0.96      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.78/0.96      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X3))
% 2.78/0.96      | ~ m1_pre_topc(X0,X3)
% 2.78/0.96      | ~ m1_pre_topc(X3,X2)
% 2.78/0.96      | v2_struct_0(X0)
% 2.78/0.96      | v2_struct_0(X1)
% 2.78/0.96      | v2_struct_0(X2)
% 2.78/0.96      | v2_struct_0(X3)
% 2.78/0.96      | ~ v2_pre_topc(X1)
% 2.78/0.96      | ~ v2_pre_topc(X2)
% 2.78/0.96      | ~ l1_pre_topc(X1)
% 2.78/0.96      | ~ l1_pre_topc(X2)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X3) != u1_struct_0(sK7) ),
% 2.78/0.96      inference(forward_subsumption_resolution,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_802,c_16,c_1]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3083,plain,
% 2.78/0.96      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 2.78/0.96      | u1_struct_0(X1) != u1_struct_0(sK7)
% 2.78/0.96      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK8),X4) != iProver_top
% 2.78/0.96      | r1_tmap_1(X1,X0,sK8,X4) = iProver_top
% 2.78/0.96      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.78/0.96      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.78/0.96      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
% 2.78/0.96      | m1_pre_topc(X2,X1) != iProver_top
% 2.78/0.96      | m1_pre_topc(X1,X3) != iProver_top
% 2.78/0.96      | v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_struct_0(X2) = iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | v2_struct_0(X3) = iProver_top
% 2.78/0.96      | v2_pre_topc(X0) != iProver_top
% 2.78/0.96      | v2_pre_topc(X3) != iProver_top
% 2.78/0.96      | l1_pre_topc(X0) != iProver_top
% 2.78/0.96      | l1_pre_topc(X3) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4036,plain,
% 2.78/0.96      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 2.78/0.96      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 2.78/0.96      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 2.78/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.78/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.78/0.96      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 2.78/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_struct_0(X2) = iProver_top
% 2.78/0.96      | v2_struct_0(sK5) = iProver_top
% 2.78/0.96      | v2_pre_topc(X2) != iProver_top
% 2.78/0.96      | v2_pre_topc(sK5) != iProver_top
% 2.78/0.96      | l1_pre_topc(X2) != iProver_top
% 2.78/0.96      | l1_pre_topc(sK5) != iProver_top ),
% 2.78/0.96      inference(equality_resolution,[status(thm)],[c_3083]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_47,negated_conjecture,
% 2.78/0.96      ( ~ v2_struct_0(sK5) ),
% 2.78/0.96      inference(cnf_transformation,[],[f101]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_54,plain,
% 2.78/0.96      ( v2_struct_0(sK5) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_46,negated_conjecture,
% 2.78/0.96      ( v2_pre_topc(sK5) ),
% 2.78/0.96      inference(cnf_transformation,[],[f102]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_55,plain,
% 2.78/0.96      ( v2_pre_topc(sK5) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_45,negated_conjecture,
% 2.78/0.96      ( l1_pre_topc(sK5) ),
% 2.78/0.96      inference(cnf_transformation,[],[f103]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_56,plain,
% 2.78/0.96      ( l1_pre_topc(sK5) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4129,plain,
% 2.78/0.96      ( l1_pre_topc(X2) != iProver_top
% 2.78/0.96      | v2_struct_0(X2) = iProver_top
% 2.78/0.96      | v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 2.78/0.96      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 2.78/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.78/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.78/0.96      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 2.78/0.96      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 2.78/0.96      | u1_struct_0(X0) != u1_struct_0(sK7)
% 2.78/0.96      | v2_pre_topc(X2) != iProver_top ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_4036,c_54,c_55,c_56]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4130,plain,
% 2.78/0.96      ( u1_struct_0(X0) != u1_struct_0(sK7)
% 2.78/0.96      | r1_tmap_1(X1,sK5,k3_tmap_1(X2,sK5,X0,X1,sK8),X3) != iProver_top
% 2.78/0.96      | r1_tmap_1(X0,sK5,sK8,X3) = iProver_top
% 2.78/0.96      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.78/0.96      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.78/0.96      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X1),u1_pre_topc(X0)) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,X2) != iProver_top
% 2.78/0.96      | m1_pre_topc(X1,X0) != iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_struct_0(X2) = iProver_top
% 2.78/0.96      | v2_pre_topc(X2) != iProver_top
% 2.78/0.96      | l1_pre_topc(X2) != iProver_top ),
% 2.78/0.96      inference(renaming,[status(thm)],[c_4129]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4147,plain,
% 2.78/0.96      ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 2.78/0.96      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 2.78/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.78/0.96      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 2.78/0.96      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,sK7) != iProver_top
% 2.78/0.96      | m1_pre_topc(sK7,X1) != iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_struct_0(sK7) = iProver_top
% 2.78/0.96      | v2_pre_topc(X1) != iProver_top
% 2.78/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.78/0.96      inference(equality_resolution,[status(thm)],[c_4130]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_42,negated_conjecture,
% 2.78/0.96      ( ~ v2_struct_0(sK7) ),
% 2.78/0.96      inference(cnf_transformation,[],[f106]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_59,plain,
% 2.78/0.96      ( v2_struct_0(sK7) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_38,negated_conjecture,
% 2.78/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 2.78/0.96      inference(cnf_transformation,[],[f110]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_63,plain,
% 2.78/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4557,plain,
% 2.78/0.96      ( v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | m1_pre_topc(sK7,X1) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,sK7) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 2.78/0.96      | r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 2.78/0.96      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 2.78/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.78/0.96      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 2.78/0.96      | v2_pre_topc(X1) != iProver_top
% 2.78/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_4147,c_59,c_63]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4558,plain,
% 2.78/0.96      ( r1_tmap_1(X0,sK5,k3_tmap_1(X1,sK5,sK7,X0,sK8),X2) != iProver_top
% 2.78/0.96      | r1_tmap_1(sK7,sK5,sK8,X2) = iProver_top
% 2.78/0.96      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.78/0.96      | m1_subset_1(X2,u1_struct_0(sK7)) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,sK7) != iProver_top
% 2.78/0.96      | m1_pre_topc(sK7,X1) != iProver_top
% 2.78/0.96      | v2_struct_0(X1) = iProver_top
% 2.78/0.96      | v2_struct_0(X0) = iProver_top
% 2.78/0.96      | v2_pre_topc(X1) != iProver_top
% 2.78/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.78/0.96      inference(renaming,[status(thm)],[c_4557]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4574,plain,
% 2.78/0.96      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 2.78/0.96      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 2.78/0.96      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 2.78/0.96      | m1_pre_topc(sK6,sK7) != iProver_top
% 2.78/0.96      | m1_pre_topc(sK7,sK4) != iProver_top
% 2.78/0.96      | v2_struct_0(sK4) = iProver_top
% 2.78/0.96      | v2_struct_0(sK6) = iProver_top
% 2.78/0.96      | v2_pre_topc(sK4) != iProver_top
% 2.78/0.96      | l1_pre_topc(sK4) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_3161,c_4558]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_50,negated_conjecture,
% 2.78/0.96      ( ~ v2_struct_0(sK4) ),
% 2.78/0.96      inference(cnf_transformation,[],[f98]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_51,plain,
% 2.78/0.96      ( v2_struct_0(sK4) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_44,negated_conjecture,
% 2.78/0.96      ( ~ v2_struct_0(sK6) ),
% 2.78/0.96      inference(cnf_transformation,[],[f104]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_57,plain,
% 2.78/0.96      ( v2_struct_0(sK6) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_60,plain,
% 2.78/0.96      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_36,negated_conjecture,
% 2.78/0.96      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 2.78/0.96      inference(cnf_transformation,[],[f112]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_64,plain,
% 2.78/0.96      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_32,negated_conjecture,
% 2.78/0.96      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 2.78/0.96      inference(cnf_transformation,[],[f116]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_67,plain,
% 2.78/0.96      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_35,negated_conjecture,
% 2.78/0.96      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 2.78/0.96      inference(cnf_transformation,[],[f113]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3097,plain,
% 2.78/0.96      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3148,plain,
% 2.78/0.96      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 2.78/0.96      inference(light_normalisation,[status(thm)],[c_3097,c_34]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4688,plain,
% 2.78/0.96      ( m1_pre_topc(sK6,sK7) != iProver_top
% 2.78/0.96      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_4574,c_51,c_52,c_53,c_57,c_60,c_64,c_67,c_3148]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4689,plain,
% 2.78/0.96      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 2.78/0.96      | m1_pre_topc(sK6,sK7) != iProver_top ),
% 2.78/0.96      inference(renaming,[status(thm)],[c_4688]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_28,plain,
% 2.78/0.96      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.78/0.96      inference(cnf_transformation,[],[f94]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3101,plain,
% 2.78/0.96      ( m1_pre_topc(X0,X0) = iProver_top
% 2.78/0.96      | l1_pre_topc(X0) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_23,plain,
% 2.78/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.78/0.96      | ~ l1_pre_topc(X0)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(cnf_transformation,[],[f88]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_281,plain,
% 2.78/0.96      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.78/0.96      | ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(global_propositional_subsumption,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_23,c_16]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_282,plain,
% 2.78/0.96      ( ~ m1_pre_topc(X0,X1)
% 2.78/0.96      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.78/0.96      | ~ l1_pre_topc(X1) ),
% 2.78/0.96      inference(renaming,[status(thm)],[c_281]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_3084,plain,
% 2.78/0.96      ( m1_pre_topc(X0,X1) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 2.78/0.96      | l1_pre_topc(X1) != iProver_top ),
% 2.78/0.96      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4155,plain,
% 2.78/0.96      ( m1_pre_topc(X0,sK6) != iProver_top
% 2.78/0.96      | m1_pre_topc(X0,sK7) = iProver_top
% 2.78/0.96      | l1_pre_topc(sK6) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_37,c_3084]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(c_4435,plain,
% 2.78/0.96      ( m1_pre_topc(sK6,sK7) = iProver_top
% 2.78/0.96      | l1_pre_topc(sK6) != iProver_top ),
% 2.78/0.96      inference(superposition,[status(thm)],[c_3101,c_4155]) ).
% 2.78/0.96  
% 2.78/0.96  cnf(contradiction,plain,
% 2.78/0.96      ( $false ),
% 2.78/0.96      inference(minisat,
% 2.78/0.96                [status(thm)],
% 2.78/0.96                [c_7117,c_6509,c_4962,c_4689,c_4435,c_53,c_52]) ).
% 2.78/0.96  
% 2.78/0.96  
% 2.78/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.96  
% 2.78/0.96  ------                               Statistics
% 2.78/0.96  
% 2.78/0.96  ------ General
% 2.78/0.96  
% 2.78/0.96  abstr_ref_over_cycles:                  0
% 2.78/0.96  abstr_ref_under_cycles:                 0
% 2.78/0.96  gc_basic_clause_elim:                   0
% 2.78/0.96  forced_gc_time:                         0
% 2.78/0.96  parsing_time:                           0.01
% 2.78/0.96  unif_index_cands_time:                  0.
% 2.78/0.96  unif_index_add_time:                    0.
% 2.78/0.96  orderings_time:                         0.
% 2.78/0.96  out_proof_time:                         0.014
% 2.78/0.96  total_time:                             0.259
% 2.78/0.96  num_of_symbols:                         63
% 2.78/0.96  num_of_terms:                           5647
% 2.78/0.96  
% 2.78/0.96  ------ Preprocessing
% 2.78/0.96  
% 2.78/0.96  num_of_splits:                          0
% 2.78/0.96  num_of_split_atoms:                     0
% 2.78/0.96  num_of_reused_defs:                     0
% 2.78/0.96  num_eq_ax_congr_red:                    15
% 2.78/0.96  num_of_sem_filtered_clauses:            1
% 2.78/0.96  num_of_subtypes:                        0
% 2.78/0.96  monotx_restored_types:                  0
% 2.78/0.96  sat_num_of_epr_types:                   0
% 2.78/0.96  sat_num_of_non_cyclic_types:            0
% 2.78/0.96  sat_guarded_non_collapsed_types:        0
% 2.78/0.96  num_pure_diseq_elim:                    0
% 2.78/0.96  simp_replaced_by:                       0
% 2.78/0.96  res_preprocessed:                       221
% 2.78/0.96  prep_upred:                             0
% 2.78/0.96  prep_unflattend:                        26
% 2.78/0.96  smt_new_axioms:                         0
% 2.78/0.96  pred_elim_cands:                        10
% 2.78/0.96  pred_elim:                              4
% 2.78/0.96  pred_elim_cl:                           6
% 2.78/0.96  pred_elim_cycles:                       10
% 2.78/0.96  merged_defs:                            0
% 2.78/0.96  merged_defs_ncl:                        0
% 2.78/0.96  bin_hyper_res:                          0
% 2.78/0.96  prep_cycles:                            4
% 2.78/0.96  pred_elim_time:                         0.045
% 2.78/0.96  splitting_time:                         0.
% 2.78/0.96  sem_filter_time:                        0.
% 2.78/0.96  monotx_time:                            0.001
% 2.78/0.96  subtype_inf_time:                       0.
% 2.78/0.96  
% 2.78/0.96  ------ Problem properties
% 2.78/0.96  
% 2.78/0.96  clauses:                                44
% 2.78/0.96  conjectures:                            17
% 2.78/0.96  epr:                                    17
% 2.78/0.96  horn:                                   36
% 2.78/0.96  ground:                                 17
% 2.78/0.96  unary:                                  17
% 2.78/0.96  binary:                                 7
% 2.78/0.96  lits:                                   136
% 2.78/0.96  lits_eq:                                11
% 2.78/0.96  fd_pure:                                0
% 2.78/0.96  fd_pseudo:                              0
% 2.78/0.96  fd_cond:                                0
% 2.78/0.96  fd_pseudo_cond:                         2
% 2.78/0.96  ac_symbols:                             0
% 2.78/0.96  
% 2.78/0.96  ------ Propositional Solver
% 2.78/0.96  
% 2.78/0.96  prop_solver_calls:                      28
% 2.78/0.96  prop_fast_solver_calls:                 2143
% 2.78/0.96  smt_solver_calls:                       0
% 2.78/0.96  smt_fast_solver_calls:                  0
% 2.78/0.96  prop_num_of_clauses:                    1768
% 2.78/0.96  prop_preprocess_simplified:             8131
% 2.78/0.96  prop_fo_subsumed:                       43
% 2.78/0.96  prop_solver_time:                       0.
% 2.78/0.96  smt_solver_time:                        0.
% 2.78/0.96  smt_fast_solver_time:                   0.
% 2.78/0.96  prop_fast_solver_time:                  0.
% 2.78/0.96  prop_unsat_core_time:                   0.
% 2.78/0.96  
% 2.78/0.96  ------ QBF
% 2.78/0.96  
% 2.78/0.96  qbf_q_res:                              0
% 2.78/0.96  qbf_num_tautologies:                    0
% 2.78/0.96  qbf_prep_cycles:                        0
% 2.78/0.96  
% 2.78/0.96  ------ BMC1
% 2.78/0.96  
% 2.78/0.96  bmc1_current_bound:                     -1
% 2.78/0.96  bmc1_last_solved_bound:                 -1
% 2.78/0.96  bmc1_unsat_core_size:                   -1
% 2.78/0.96  bmc1_unsat_core_parents_size:           -1
% 2.78/0.96  bmc1_merge_next_fun:                    0
% 2.78/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.78/0.96  
% 2.78/0.96  ------ Instantiation
% 2.78/0.96  
% 2.78/0.96  inst_num_of_clauses:                    533
% 2.78/0.96  inst_num_in_passive:                    152
% 2.78/0.96  inst_num_in_active:                     381
% 2.78/0.96  inst_num_in_unprocessed:                0
% 2.78/0.96  inst_num_of_loops:                      400
% 2.78/0.96  inst_num_of_learning_restarts:          0
% 2.78/0.96  inst_num_moves_active_passive:          16
% 2.78/0.96  inst_lit_activity:                      0
% 2.78/0.96  inst_lit_activity_moves:                0
% 2.78/0.96  inst_num_tautologies:                   0
% 2.78/0.96  inst_num_prop_implied:                  0
% 2.78/0.96  inst_num_existing_simplified:           0
% 2.78/0.96  inst_num_eq_res_simplified:             0
% 2.78/0.96  inst_num_child_elim:                    0
% 2.78/0.96  inst_num_of_dismatching_blockings:      384
% 2.78/0.96  inst_num_of_non_proper_insts:           912
% 2.78/0.96  inst_num_of_duplicates:                 0
% 2.78/0.96  inst_inst_num_from_inst_to_res:         0
% 2.78/0.96  inst_dismatching_checking_time:         0.
% 2.78/0.96  
% 2.78/0.97  ------ Resolution
% 2.78/0.97  
% 2.78/0.97  res_num_of_clauses:                     0
% 2.78/0.97  res_num_in_passive:                     0
% 2.78/0.97  res_num_in_active:                      0
% 2.78/0.97  res_num_of_loops:                       225
% 2.78/0.97  res_forward_subset_subsumed:            70
% 2.78/0.97  res_backward_subset_subsumed:           2
% 2.78/0.97  res_forward_subsumed:                   0
% 2.78/0.97  res_backward_subsumed:                  0
% 2.78/0.97  res_forward_subsumption_resolution:     6
% 2.78/0.97  res_backward_subsumption_resolution:    0
% 2.78/0.97  res_clause_to_clause_subsumption:       324
% 2.78/0.97  res_orphan_elimination:                 0
% 2.78/0.97  res_tautology_del:                      105
% 2.78/0.97  res_num_eq_res_simplified:              0
% 2.78/0.97  res_num_sel_changes:                    0
% 2.78/0.97  res_moves_from_active_to_pass:          0
% 2.78/0.97  
% 2.78/0.97  ------ Superposition
% 2.78/0.97  
% 2.78/0.97  sup_time_total:                         0.
% 2.78/0.97  sup_time_generating:                    0.
% 2.78/0.97  sup_time_sim_full:                      0.
% 2.78/0.97  sup_time_sim_immed:                     0.
% 2.78/0.97  
% 2.78/0.97  sup_num_of_clauses:                     92
% 2.78/0.97  sup_num_in_active:                      72
% 2.78/0.97  sup_num_in_passive:                     20
% 2.78/0.97  sup_num_of_loops:                       78
% 2.78/0.97  sup_fw_superposition:                   50
% 2.78/0.97  sup_bw_superposition:                   40
% 2.78/0.97  sup_immediate_simplified:               14
% 2.78/0.97  sup_given_eliminated:                   0
% 2.78/0.97  comparisons_done:                       0
% 2.78/0.97  comparisons_avoided:                    0
% 2.78/0.97  
% 2.78/0.97  ------ Simplifications
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  sim_fw_subset_subsumed:                 13
% 2.78/0.97  sim_bw_subset_subsumed:                 5
% 2.78/0.97  sim_fw_subsumed:                        3
% 2.78/0.97  sim_bw_subsumed:                        0
% 2.78/0.97  sim_fw_subsumption_res:                 0
% 2.78/0.97  sim_bw_subsumption_res:                 0
% 2.78/0.97  sim_tautology_del:                      12
% 2.78/0.97  sim_eq_tautology_del:                   4
% 2.78/0.97  sim_eq_res_simp:                        0
% 2.78/0.97  sim_fw_demodulated:                     0
% 2.78/0.97  sim_bw_demodulated:                     4
% 2.78/0.97  sim_light_normalised:                   5
% 2.78/0.97  sim_joinable_taut:                      0
% 2.78/0.97  sim_joinable_simp:                      0
% 2.78/0.97  sim_ac_normalised:                      0
% 2.78/0.97  sim_smt_subsumption:                    0
% 2.78/0.97  
%------------------------------------------------------------------------------
