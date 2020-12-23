%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:27 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  244 (1439 expanded)
%              Number of clauses        :  144 ( 326 expanded)
%              Number of leaves         :   27 ( 630 expanded)
%              Depth                    :   26
%              Number of atoms          : 1395 (20268 expanded)
%              Number of equality atoms :  439 (3071 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f68,plain,(
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

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,
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

fof(f69,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f55,f68,f67,f66,f65,f64,f63,f62])).

fof(f109,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f113,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f69])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f107,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f69])).

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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

fof(f110,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f104,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f105,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

fof(f112,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f69])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f101,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f117,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f69])).

fof(f116,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f69])).

fof(f17,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,axiom,(
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
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f50])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(nnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f61])).

fof(f122,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(equality_resolution,[],[f98])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f89,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f118,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f69])).

fof(f114,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f69])).

fof(f106,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1862,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_26,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1869,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_272,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_6])).

cnf(c_273,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_1852,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_4789,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1852])).

cnf(c_46,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_51,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1860,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1883,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3475,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1860,c_1883])).

cnf(c_4916,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4789,c_51,c_3475])).

cnf(c_4917,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4916])).

cnf(c_4924,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_4917])).

cnf(c_5177,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4924,c_51,c_3475])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_644,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_645,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_38])).

cnf(c_650,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_649])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_681,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_650,c_29])).

cnf(c_1850,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_3197,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,sK1,X0,X1,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1850])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_52,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_53,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_54,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3915,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,sK1,X0,X1,sK4)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3197,c_52,c_53,c_54])).

cnf(c_3916,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,sK1,X0,X1,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3915])).

cnf(c_3927,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3916])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_61,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5999,plain,
    ( m1_pre_topc(sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3927,c_61])).

cnf(c_6000,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5999])).

cnf(c_6012,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5177,c_6000])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_695,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_37])).

cnf(c_696,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_700,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_38])).

cnf(c_701,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_1849,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_3042,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k2_tmap_1(X0,sK1,sK4,X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1849])).

cnf(c_3733,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k2_tmap_1(X0,sK1,sK4,X1)
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3042,c_52,c_53,c_54])).

cnf(c_3734,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k2_tmap_1(X0,sK1,sK4,X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3733])).

cnf(c_3744,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3734])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_57,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3474,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1883])).

cnf(c_3865,plain,
    ( v2_pre_topc(sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3744,c_51,c_57,c_61,c_3474])).

cnf(c_3866,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3865])).

cnf(c_5183,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5177,c_3866])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_50,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_58,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3224,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4173,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3224])).

cnf(c_4174,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4173])).

cnf(c_5249,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5183,c_50,c_51,c_58,c_4174])).

cnf(c_6018,plain,
    ( k3_tmap_1(X0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6012,c_5249])).

cnf(c_9376,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_6018])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_49,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_10178,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9376,c_49,c_50,c_51])).

cnf(c_31,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1866,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1933,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1866,c_32])).

cnf(c_10181,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10178,c_1933])).

cnf(c_23,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_262,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_25])).

cnf(c_263,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_27,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_588,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(u1_struct_0(X5),X6)
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X4 != X5
    | X0 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_263,c_27])).

cnf(c_589,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(u1_struct_0(X4),X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_625,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(u1_struct_0(X4),X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_589,c_12])).

cnf(c_740,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v3_pre_topc(u1_struct_0(X4),X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_625,c_37])).

cnf(c_741,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ v3_pre_topc(u1_struct_0(X0),X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(u1_struct_0(X0),X2)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_38])).

cnf(c_746,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ v3_pre_topc(u1_struct_0(X0),X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_1848,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) != iProver_top
    | r1_tmap_1(X1,X0,sK4,X3) = iProver_top
    | v3_pre_topc(u1_struct_0(X2),X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_3180,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1848])).

cnf(c_1141,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2274,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_2565,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),X2)
    | r1_tmap_1(sK3,X1,sK4,X2)
    | ~ v3_pre_topc(u1_struct_0(X0),sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_2566,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2565])).

cnf(c_3842,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3180,c_51,c_57,c_2274,c_2566,c_3474])).

cnf(c_3843,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3842])).

cnf(c_3860,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3843])).

cnf(c_5383,plain,
    ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_50,c_51,c_52,c_53,c_54,c_58,c_61,c_4174])).

cnf(c_5384,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5383])).

cnf(c_10185,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_10181,c_5384])).

cnf(c_1884,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6182,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1860,c_1884])).

cnf(c_7005,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6182,c_50,c_51])).

cnf(c_9,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1880,plain,
    ( v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4212,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1880])).

cnf(c_4215,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4212,c_51,c_3475])).

cnf(c_7010,plain,
    ( v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7005,c_4215])).

cnf(c_3601,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3474,c_51])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1885,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4075,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3601,c_1885])).

cnf(c_7014,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_7010,c_4075])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1878,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5513,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1878])).

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3683,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3688,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3683])).

cnf(c_5514,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1878])).

cnf(c_5652,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(X0,X1) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5513,c_51,c_3475,c_3688,c_5514])).

cnf(c_5653,plain,
    ( g1_pre_topc(X0,X1) != sK3
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_5652])).

cnf(c_7094,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_7014,c_5653])).

cnf(c_10186,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10185,c_7094])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_497,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_1851,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_3978,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3601,c_1851])).

cnf(c_19,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1871,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4677,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3978,c_1871])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_65,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_62,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_55,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10186,c_4924,c_4677,c_4174,c_3475,c_3474,c_65,c_62,c_58,c_55,c_51,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.54/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/1.00  
% 3.54/1.00  ------  iProver source info
% 3.54/1.00  
% 3.54/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.54/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/1.00  git: non_committed_changes: false
% 3.54/1.00  git: last_make_outside_of_git: false
% 3.54/1.00  
% 3.54/1.00  ------ 
% 3.54/1.00  
% 3.54/1.00  ------ Input Options
% 3.54/1.00  
% 3.54/1.00  --out_options                           all
% 3.54/1.00  --tptp_safe_out                         true
% 3.54/1.00  --problem_path                          ""
% 3.54/1.00  --include_path                          ""
% 3.54/1.00  --clausifier                            res/vclausify_rel
% 3.54/1.00  --clausifier_options                    --mode clausify
% 3.54/1.00  --stdin                                 false
% 3.54/1.00  --stats_out                             all
% 3.54/1.00  
% 3.54/1.00  ------ General Options
% 3.54/1.00  
% 3.54/1.00  --fof                                   false
% 3.54/1.00  --time_out_real                         305.
% 3.54/1.00  --time_out_virtual                      -1.
% 3.54/1.00  --symbol_type_check                     false
% 3.54/1.00  --clausify_out                          false
% 3.54/1.00  --sig_cnt_out                           false
% 3.54/1.00  --trig_cnt_out                          false
% 3.54/1.00  --trig_cnt_out_tolerance                1.
% 3.54/1.00  --trig_cnt_out_sk_spl                   false
% 3.54/1.00  --abstr_cl_out                          false
% 3.54/1.00  
% 3.54/1.00  ------ Global Options
% 3.54/1.00  
% 3.54/1.00  --schedule                              default
% 3.54/1.00  --add_important_lit                     false
% 3.54/1.00  --prop_solver_per_cl                    1000
% 3.54/1.00  --min_unsat_core                        false
% 3.54/1.00  --soft_assumptions                      false
% 3.54/1.00  --soft_lemma_size                       3
% 3.54/1.00  --prop_impl_unit_size                   0
% 3.54/1.00  --prop_impl_unit                        []
% 3.54/1.00  --share_sel_clauses                     true
% 3.54/1.00  --reset_solvers                         false
% 3.54/1.00  --bc_imp_inh                            [conj_cone]
% 3.54/1.00  --conj_cone_tolerance                   3.
% 3.54/1.00  --extra_neg_conj                        none
% 3.54/1.00  --large_theory_mode                     true
% 3.54/1.00  --prolific_symb_bound                   200
% 3.54/1.00  --lt_threshold                          2000
% 3.54/1.00  --clause_weak_htbl                      true
% 3.54/1.00  --gc_record_bc_elim                     false
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing Options
% 3.54/1.00  
% 3.54/1.00  --preprocessing_flag                    true
% 3.54/1.00  --time_out_prep_mult                    0.1
% 3.54/1.00  --splitting_mode                        input
% 3.54/1.00  --splitting_grd                         true
% 3.54/1.00  --splitting_cvd                         false
% 3.54/1.00  --splitting_cvd_svl                     false
% 3.54/1.00  --splitting_nvd                         32
% 3.54/1.00  --sub_typing                            true
% 3.54/1.00  --prep_gs_sim                           true
% 3.54/1.00  --prep_unflatten                        true
% 3.54/1.00  --prep_res_sim                          true
% 3.54/1.00  --prep_upred                            true
% 3.54/1.00  --prep_sem_filter                       exhaustive
% 3.54/1.00  --prep_sem_filter_out                   false
% 3.54/1.00  --pred_elim                             true
% 3.54/1.00  --res_sim_input                         true
% 3.54/1.00  --eq_ax_congr_red                       true
% 3.54/1.00  --pure_diseq_elim                       true
% 3.54/1.00  --brand_transform                       false
% 3.54/1.00  --non_eq_to_eq                          false
% 3.54/1.00  --prep_def_merge                        true
% 3.54/1.00  --prep_def_merge_prop_impl              false
% 3.54/1.00  --prep_def_merge_mbd                    true
% 3.54/1.00  --prep_def_merge_tr_red                 false
% 3.54/1.00  --prep_def_merge_tr_cl                  false
% 3.54/1.00  --smt_preprocessing                     true
% 3.54/1.00  --smt_ac_axioms                         fast
% 3.54/1.00  --preprocessed_out                      false
% 3.54/1.00  --preprocessed_stats                    false
% 3.54/1.00  
% 3.54/1.00  ------ Abstraction refinement Options
% 3.54/1.00  
% 3.54/1.00  --abstr_ref                             []
% 3.54/1.00  --abstr_ref_prep                        false
% 3.54/1.00  --abstr_ref_until_sat                   false
% 3.54/1.00  --abstr_ref_sig_restrict                funpre
% 3.54/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.00  --abstr_ref_under                       []
% 3.54/1.00  
% 3.54/1.00  ------ SAT Options
% 3.54/1.00  
% 3.54/1.00  --sat_mode                              false
% 3.54/1.00  --sat_fm_restart_options                ""
% 3.54/1.00  --sat_gr_def                            false
% 3.54/1.00  --sat_epr_types                         true
% 3.54/1.00  --sat_non_cyclic_types                  false
% 3.54/1.00  --sat_finite_models                     false
% 3.54/1.00  --sat_fm_lemmas                         false
% 3.54/1.00  --sat_fm_prep                           false
% 3.54/1.00  --sat_fm_uc_incr                        true
% 3.54/1.00  --sat_out_model                         small
% 3.54/1.00  --sat_out_clauses                       false
% 3.54/1.00  
% 3.54/1.00  ------ QBF Options
% 3.54/1.00  
% 3.54/1.00  --qbf_mode                              false
% 3.54/1.00  --qbf_elim_univ                         false
% 3.54/1.00  --qbf_dom_inst                          none
% 3.54/1.00  --qbf_dom_pre_inst                      false
% 3.54/1.00  --qbf_sk_in                             false
% 3.54/1.00  --qbf_pred_elim                         true
% 3.54/1.00  --qbf_split                             512
% 3.54/1.00  
% 3.54/1.00  ------ BMC1 Options
% 3.54/1.00  
% 3.54/1.00  --bmc1_incremental                      false
% 3.54/1.00  --bmc1_axioms                           reachable_all
% 3.54/1.00  --bmc1_min_bound                        0
% 3.54/1.00  --bmc1_max_bound                        -1
% 3.54/1.00  --bmc1_max_bound_default                -1
% 3.54/1.00  --bmc1_symbol_reachability              true
% 3.54/1.00  --bmc1_property_lemmas                  false
% 3.54/1.00  --bmc1_k_induction                      false
% 3.54/1.00  --bmc1_non_equiv_states                 false
% 3.54/1.00  --bmc1_deadlock                         false
% 3.54/1.00  --bmc1_ucm                              false
% 3.54/1.00  --bmc1_add_unsat_core                   none
% 3.54/1.00  --bmc1_unsat_core_children              false
% 3.54/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.00  --bmc1_out_stat                         full
% 3.54/1.00  --bmc1_ground_init                      false
% 3.54/1.00  --bmc1_pre_inst_next_state              false
% 3.54/1.00  --bmc1_pre_inst_state                   false
% 3.54/1.00  --bmc1_pre_inst_reach_state             false
% 3.54/1.00  --bmc1_out_unsat_core                   false
% 3.54/1.00  --bmc1_aig_witness_out                  false
% 3.54/1.00  --bmc1_verbose                          false
% 3.54/1.00  --bmc1_dump_clauses_tptp                false
% 3.54/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.00  --bmc1_dump_file                        -
% 3.54/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.00  --bmc1_ucm_extend_mode                  1
% 3.54/1.00  --bmc1_ucm_init_mode                    2
% 3.54/1.00  --bmc1_ucm_cone_mode                    none
% 3.54/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.00  --bmc1_ucm_relax_model                  4
% 3.54/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.00  --bmc1_ucm_layered_model                none
% 3.54/1.00  --bmc1_ucm_max_lemma_size               10
% 3.54/1.00  
% 3.54/1.00  ------ AIG Options
% 3.54/1.00  
% 3.54/1.00  --aig_mode                              false
% 3.54/1.00  
% 3.54/1.00  ------ Instantiation Options
% 3.54/1.00  
% 3.54/1.00  --instantiation_flag                    true
% 3.54/1.00  --inst_sos_flag                         false
% 3.54/1.00  --inst_sos_phase                        true
% 3.54/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel_side                     num_symb
% 3.54/1.00  --inst_solver_per_active                1400
% 3.54/1.00  --inst_solver_calls_frac                1.
% 3.54/1.00  --inst_passive_queue_type               priority_queues
% 3.54/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.00  --inst_passive_queues_freq              [25;2]
% 3.54/1.00  --inst_dismatching                      true
% 3.54/1.00  --inst_eager_unprocessed_to_passive     true
% 3.54/1.00  --inst_prop_sim_given                   true
% 3.54/1.00  --inst_prop_sim_new                     false
% 3.54/1.00  --inst_subs_new                         false
% 3.54/1.00  --inst_eq_res_simp                      false
% 3.54/1.00  --inst_subs_given                       false
% 3.54/1.00  --inst_orphan_elimination               true
% 3.54/1.00  --inst_learning_loop_flag               true
% 3.54/1.00  --inst_learning_start                   3000
% 3.54/1.00  --inst_learning_factor                  2
% 3.54/1.00  --inst_start_prop_sim_after_learn       3
% 3.54/1.00  --inst_sel_renew                        solver
% 3.54/1.00  --inst_lit_activity_flag                true
% 3.54/1.00  --inst_restr_to_given                   false
% 3.54/1.00  --inst_activity_threshold               500
% 3.54/1.00  --inst_out_proof                        true
% 3.54/1.00  
% 3.54/1.00  ------ Resolution Options
% 3.54/1.00  
% 3.54/1.00  --resolution_flag                       true
% 3.54/1.00  --res_lit_sel                           adaptive
% 3.54/1.00  --res_lit_sel_side                      none
% 3.54/1.00  --res_ordering                          kbo
% 3.54/1.00  --res_to_prop_solver                    active
% 3.54/1.00  --res_prop_simpl_new                    false
% 3.54/1.00  --res_prop_simpl_given                  true
% 3.54/1.00  --res_passive_queue_type                priority_queues
% 3.54/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.00  --res_passive_queues_freq               [15;5]
% 3.54/1.00  --res_forward_subs                      full
% 3.54/1.00  --res_backward_subs                     full
% 3.54/1.00  --res_forward_subs_resolution           true
% 3.54/1.00  --res_backward_subs_resolution          true
% 3.54/1.00  --res_orphan_elimination                true
% 3.54/1.00  --res_time_limit                        2.
% 3.54/1.00  --res_out_proof                         true
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Options
% 3.54/1.00  
% 3.54/1.00  --superposition_flag                    true
% 3.54/1.00  --sup_passive_queue_type                priority_queues
% 3.54/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.00  --demod_completeness_check              fast
% 3.54/1.00  --demod_use_ground                      true
% 3.54/1.00  --sup_to_prop_solver                    passive
% 3.54/1.00  --sup_prop_simpl_new                    true
% 3.54/1.00  --sup_prop_simpl_given                  true
% 3.54/1.00  --sup_fun_splitting                     false
% 3.54/1.00  --sup_smt_interval                      50000
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Simplification Setup
% 3.54/1.00  
% 3.54/1.00  --sup_indices_passive                   []
% 3.54/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_full_bw                           [BwDemod]
% 3.54/1.00  --sup_immed_triv                        [TrivRules]
% 3.54/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_immed_bw_main                     []
% 3.54/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  
% 3.54/1.00  ------ Combination Options
% 3.54/1.00  
% 3.54/1.00  --comb_res_mult                         3
% 3.54/1.00  --comb_sup_mult                         2
% 3.54/1.00  --comb_inst_mult                        10
% 3.54/1.00  
% 3.54/1.00  ------ Debug Options
% 3.54/1.00  
% 3.54/1.00  --dbg_backtrace                         false
% 3.54/1.00  --dbg_dump_prop_clauses                 false
% 3.54/1.00  --dbg_dump_prop_clauses_file            -
% 3.54/1.00  --dbg_out_stat                          false
% 3.54/1.00  ------ Parsing...
% 3.54/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/1.00  ------ Proving...
% 3.54/1.00  ------ Problem Properties 
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  clauses                                 43
% 3.54/1.00  conjectures                             17
% 3.54/1.00  EPR                                     16
% 3.54/1.00  Horn                                    38
% 3.54/1.00  unary                                   19
% 3.54/1.00  binary                                  3
% 3.54/1.00  lits                                    144
% 3.54/1.00  lits eq                                 19
% 3.54/1.00  fd_pure                                 0
% 3.54/1.00  fd_pseudo                               0
% 3.54/1.00  fd_cond                                 0
% 3.54/1.00  fd_pseudo_cond                          2
% 3.54/1.00  AC symbols                              0
% 3.54/1.00  
% 3.54/1.00  ------ Schedule dynamic 5 is on 
% 3.54/1.00  
% 3.54/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  ------ 
% 3.54/1.00  Current options:
% 3.54/1.00  ------ 
% 3.54/1.00  
% 3.54/1.00  ------ Input Options
% 3.54/1.00  
% 3.54/1.00  --out_options                           all
% 3.54/1.00  --tptp_safe_out                         true
% 3.54/1.00  --problem_path                          ""
% 3.54/1.00  --include_path                          ""
% 3.54/1.00  --clausifier                            res/vclausify_rel
% 3.54/1.00  --clausifier_options                    --mode clausify
% 3.54/1.00  --stdin                                 false
% 3.54/1.00  --stats_out                             all
% 3.54/1.00  
% 3.54/1.00  ------ General Options
% 3.54/1.00  
% 3.54/1.00  --fof                                   false
% 3.54/1.00  --time_out_real                         305.
% 3.54/1.00  --time_out_virtual                      -1.
% 3.54/1.00  --symbol_type_check                     false
% 3.54/1.00  --clausify_out                          false
% 3.54/1.00  --sig_cnt_out                           false
% 3.54/1.00  --trig_cnt_out                          false
% 3.54/1.00  --trig_cnt_out_tolerance                1.
% 3.54/1.00  --trig_cnt_out_sk_spl                   false
% 3.54/1.00  --abstr_cl_out                          false
% 3.54/1.00  
% 3.54/1.00  ------ Global Options
% 3.54/1.00  
% 3.54/1.00  --schedule                              default
% 3.54/1.00  --add_important_lit                     false
% 3.54/1.00  --prop_solver_per_cl                    1000
% 3.54/1.00  --min_unsat_core                        false
% 3.54/1.00  --soft_assumptions                      false
% 3.54/1.00  --soft_lemma_size                       3
% 3.54/1.00  --prop_impl_unit_size                   0
% 3.54/1.00  --prop_impl_unit                        []
% 3.54/1.00  --share_sel_clauses                     true
% 3.54/1.00  --reset_solvers                         false
% 3.54/1.00  --bc_imp_inh                            [conj_cone]
% 3.54/1.00  --conj_cone_tolerance                   3.
% 3.54/1.00  --extra_neg_conj                        none
% 3.54/1.00  --large_theory_mode                     true
% 3.54/1.00  --prolific_symb_bound                   200
% 3.54/1.00  --lt_threshold                          2000
% 3.54/1.00  --clause_weak_htbl                      true
% 3.54/1.00  --gc_record_bc_elim                     false
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing Options
% 3.54/1.00  
% 3.54/1.00  --preprocessing_flag                    true
% 3.54/1.00  --time_out_prep_mult                    0.1
% 3.54/1.00  --splitting_mode                        input
% 3.54/1.00  --splitting_grd                         true
% 3.54/1.00  --splitting_cvd                         false
% 3.54/1.00  --splitting_cvd_svl                     false
% 3.54/1.00  --splitting_nvd                         32
% 3.54/1.00  --sub_typing                            true
% 3.54/1.00  --prep_gs_sim                           true
% 3.54/1.00  --prep_unflatten                        true
% 3.54/1.00  --prep_res_sim                          true
% 3.54/1.00  --prep_upred                            true
% 3.54/1.00  --prep_sem_filter                       exhaustive
% 3.54/1.00  --prep_sem_filter_out                   false
% 3.54/1.00  --pred_elim                             true
% 3.54/1.00  --res_sim_input                         true
% 3.54/1.00  --eq_ax_congr_red                       true
% 3.54/1.00  --pure_diseq_elim                       true
% 3.54/1.00  --brand_transform                       false
% 3.54/1.00  --non_eq_to_eq                          false
% 3.54/1.00  --prep_def_merge                        true
% 3.54/1.00  --prep_def_merge_prop_impl              false
% 3.54/1.00  --prep_def_merge_mbd                    true
% 3.54/1.00  --prep_def_merge_tr_red                 false
% 3.54/1.00  --prep_def_merge_tr_cl                  false
% 3.54/1.00  --smt_preprocessing                     true
% 3.54/1.00  --smt_ac_axioms                         fast
% 3.54/1.00  --preprocessed_out                      false
% 3.54/1.00  --preprocessed_stats                    false
% 3.54/1.00  
% 3.54/1.00  ------ Abstraction refinement Options
% 3.54/1.00  
% 3.54/1.00  --abstr_ref                             []
% 3.54/1.00  --abstr_ref_prep                        false
% 3.54/1.00  --abstr_ref_until_sat                   false
% 3.54/1.00  --abstr_ref_sig_restrict                funpre
% 3.54/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/1.00  --abstr_ref_under                       []
% 3.54/1.00  
% 3.54/1.00  ------ SAT Options
% 3.54/1.00  
% 3.54/1.00  --sat_mode                              false
% 3.54/1.00  --sat_fm_restart_options                ""
% 3.54/1.00  --sat_gr_def                            false
% 3.54/1.00  --sat_epr_types                         true
% 3.54/1.00  --sat_non_cyclic_types                  false
% 3.54/1.00  --sat_finite_models                     false
% 3.54/1.00  --sat_fm_lemmas                         false
% 3.54/1.00  --sat_fm_prep                           false
% 3.54/1.00  --sat_fm_uc_incr                        true
% 3.54/1.00  --sat_out_model                         small
% 3.54/1.00  --sat_out_clauses                       false
% 3.54/1.00  
% 3.54/1.00  ------ QBF Options
% 3.54/1.00  
% 3.54/1.00  --qbf_mode                              false
% 3.54/1.00  --qbf_elim_univ                         false
% 3.54/1.00  --qbf_dom_inst                          none
% 3.54/1.00  --qbf_dom_pre_inst                      false
% 3.54/1.00  --qbf_sk_in                             false
% 3.54/1.00  --qbf_pred_elim                         true
% 3.54/1.00  --qbf_split                             512
% 3.54/1.00  
% 3.54/1.00  ------ BMC1 Options
% 3.54/1.00  
% 3.54/1.00  --bmc1_incremental                      false
% 3.54/1.00  --bmc1_axioms                           reachable_all
% 3.54/1.00  --bmc1_min_bound                        0
% 3.54/1.00  --bmc1_max_bound                        -1
% 3.54/1.00  --bmc1_max_bound_default                -1
% 3.54/1.00  --bmc1_symbol_reachability              true
% 3.54/1.00  --bmc1_property_lemmas                  false
% 3.54/1.00  --bmc1_k_induction                      false
% 3.54/1.00  --bmc1_non_equiv_states                 false
% 3.54/1.00  --bmc1_deadlock                         false
% 3.54/1.00  --bmc1_ucm                              false
% 3.54/1.00  --bmc1_add_unsat_core                   none
% 3.54/1.00  --bmc1_unsat_core_children              false
% 3.54/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/1.00  --bmc1_out_stat                         full
% 3.54/1.00  --bmc1_ground_init                      false
% 3.54/1.00  --bmc1_pre_inst_next_state              false
% 3.54/1.00  --bmc1_pre_inst_state                   false
% 3.54/1.00  --bmc1_pre_inst_reach_state             false
% 3.54/1.00  --bmc1_out_unsat_core                   false
% 3.54/1.00  --bmc1_aig_witness_out                  false
% 3.54/1.00  --bmc1_verbose                          false
% 3.54/1.00  --bmc1_dump_clauses_tptp                false
% 3.54/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.54/1.00  --bmc1_dump_file                        -
% 3.54/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.54/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.54/1.00  --bmc1_ucm_extend_mode                  1
% 3.54/1.00  --bmc1_ucm_init_mode                    2
% 3.54/1.00  --bmc1_ucm_cone_mode                    none
% 3.54/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.54/1.00  --bmc1_ucm_relax_model                  4
% 3.54/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.54/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/1.00  --bmc1_ucm_layered_model                none
% 3.54/1.00  --bmc1_ucm_max_lemma_size               10
% 3.54/1.00  
% 3.54/1.00  ------ AIG Options
% 3.54/1.00  
% 3.54/1.00  --aig_mode                              false
% 3.54/1.00  
% 3.54/1.00  ------ Instantiation Options
% 3.54/1.00  
% 3.54/1.00  --instantiation_flag                    true
% 3.54/1.00  --inst_sos_flag                         false
% 3.54/1.00  --inst_sos_phase                        true
% 3.54/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/1.00  --inst_lit_sel_side                     none
% 3.54/1.00  --inst_solver_per_active                1400
% 3.54/1.00  --inst_solver_calls_frac                1.
% 3.54/1.00  --inst_passive_queue_type               priority_queues
% 3.54/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/1.00  --inst_passive_queues_freq              [25;2]
% 3.54/1.00  --inst_dismatching                      true
% 3.54/1.00  --inst_eager_unprocessed_to_passive     true
% 3.54/1.00  --inst_prop_sim_given                   true
% 3.54/1.00  --inst_prop_sim_new                     false
% 3.54/1.00  --inst_subs_new                         false
% 3.54/1.00  --inst_eq_res_simp                      false
% 3.54/1.00  --inst_subs_given                       false
% 3.54/1.00  --inst_orphan_elimination               true
% 3.54/1.00  --inst_learning_loop_flag               true
% 3.54/1.00  --inst_learning_start                   3000
% 3.54/1.00  --inst_learning_factor                  2
% 3.54/1.00  --inst_start_prop_sim_after_learn       3
% 3.54/1.00  --inst_sel_renew                        solver
% 3.54/1.00  --inst_lit_activity_flag                true
% 3.54/1.00  --inst_restr_to_given                   false
% 3.54/1.00  --inst_activity_threshold               500
% 3.54/1.00  --inst_out_proof                        true
% 3.54/1.00  
% 3.54/1.00  ------ Resolution Options
% 3.54/1.00  
% 3.54/1.00  --resolution_flag                       false
% 3.54/1.00  --res_lit_sel                           adaptive
% 3.54/1.00  --res_lit_sel_side                      none
% 3.54/1.00  --res_ordering                          kbo
% 3.54/1.00  --res_to_prop_solver                    active
% 3.54/1.00  --res_prop_simpl_new                    false
% 3.54/1.00  --res_prop_simpl_given                  true
% 3.54/1.00  --res_passive_queue_type                priority_queues
% 3.54/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/1.00  --res_passive_queues_freq               [15;5]
% 3.54/1.00  --res_forward_subs                      full
% 3.54/1.00  --res_backward_subs                     full
% 3.54/1.00  --res_forward_subs_resolution           true
% 3.54/1.00  --res_backward_subs_resolution          true
% 3.54/1.00  --res_orphan_elimination                true
% 3.54/1.00  --res_time_limit                        2.
% 3.54/1.00  --res_out_proof                         true
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Options
% 3.54/1.00  
% 3.54/1.00  --superposition_flag                    true
% 3.54/1.00  --sup_passive_queue_type                priority_queues
% 3.54/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.54/1.00  --demod_completeness_check              fast
% 3.54/1.00  --demod_use_ground                      true
% 3.54/1.00  --sup_to_prop_solver                    passive
% 3.54/1.00  --sup_prop_simpl_new                    true
% 3.54/1.00  --sup_prop_simpl_given                  true
% 3.54/1.00  --sup_fun_splitting                     false
% 3.54/1.00  --sup_smt_interval                      50000
% 3.54/1.00  
% 3.54/1.00  ------ Superposition Simplification Setup
% 3.54/1.00  
% 3.54/1.00  --sup_indices_passive                   []
% 3.54/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_full_bw                           [BwDemod]
% 3.54/1.00  --sup_immed_triv                        [TrivRules]
% 3.54/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_immed_bw_main                     []
% 3.54/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/1.00  
% 3.54/1.00  ------ Combination Options
% 3.54/1.00  
% 3.54/1.00  --comb_res_mult                         3
% 3.54/1.00  --comb_sup_mult                         2
% 3.54/1.00  --comb_inst_mult                        10
% 3.54/1.00  
% 3.54/1.00  ------ Debug Options
% 3.54/1.00  
% 3.54/1.00  --dbg_backtrace                         false
% 3.54/1.00  --dbg_dump_prop_clauses                 false
% 3.54/1.00  --dbg_dump_prop_clauses_file            -
% 3.54/1.00  --dbg_out_stat                          false
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  ------ Proving...
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS status Theorem for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  fof(f22,conjecture,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f23,negated_conjecture,(
% 3.54/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.54/1.00    inference(negated_conjecture,[],[f22])).
% 3.54/1.00  
% 3.54/1.00  fof(f54,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f23])).
% 3.54/1.00  
% 3.54/1.00  fof(f55,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f54])).
% 3.54/1.00  
% 3.54/1.00  fof(f68,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f67,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f66,plain,(
% 3.54/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f65,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f64,plain,(
% 3.54/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f63,plain,(
% 3.54/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f62,plain,(
% 3.54/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.54/1.00    introduced(choice_axiom,[])).
% 3.54/1.00  
% 3.54/1.00  fof(f69,plain,(
% 3.54/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.54/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f55,f68,f67,f66,f65,f64,f63,f62])).
% 3.54/1.00  
% 3.54/1.00  fof(f109,plain,(
% 3.54/1.00    m1_pre_topc(sK3,sK0)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f19,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f49,plain,(
% 3.54/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f19])).
% 3.54/1.00  
% 3.54/1.00  fof(f96,plain,(
% 3.54/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f49])).
% 3.54/1.00  
% 3.54/1.00  fof(f113,plain,(
% 3.54/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f13,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f39,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f13])).
% 3.54/1.00  
% 3.54/1.00  fof(f58,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(nnf_transformation,[],[f39])).
% 3.54/1.00  
% 3.54/1.00  fof(f87,plain,(
% 3.54/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f58])).
% 3.54/1.00  
% 3.54/1.00  fof(f7,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f30,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f7])).
% 3.54/1.00  
% 3.54/1.00  fof(f76,plain,(
% 3.54/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f30])).
% 3.54/1.00  
% 3.54/1.00  fof(f102,plain,(
% 3.54/1.00    l1_pre_topc(sK0)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f107,plain,(
% 3.54/1.00    m1_pre_topc(sK2,sK0)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f16,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f44,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f16])).
% 3.54/1.00  
% 3.54/1.00  fof(f45,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f44])).
% 3.54/1.00  
% 3.54/1.00  fof(f91,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f45])).
% 3.54/1.00  
% 3.54/1.00  fof(f111,plain,(
% 3.54/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f110,plain,(
% 3.54/1.00    v1_funct_1(sK4)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f21,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f52,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f21])).
% 3.54/1.00  
% 3.54/1.00  fof(f53,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f52])).
% 3.54/1.00  
% 3.54/1.00  fof(f99,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f53])).
% 3.54/1.00  
% 3.54/1.00  fof(f103,plain,(
% 3.54/1.00    ~v2_struct_0(sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f104,plain,(
% 3.54/1.00    v2_pre_topc(sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f105,plain,(
% 3.54/1.00    l1_pre_topc(sK1)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f112,plain,(
% 3.54/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f15,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f42,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f15])).
% 3.54/1.00  
% 3.54/1.00  fof(f43,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f42])).
% 3.54/1.00  
% 3.54/1.00  fof(f90,plain,(
% 3.54/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f43])).
% 3.54/1.00  
% 3.54/1.00  fof(f108,plain,(
% 3.54/1.00    ~v2_struct_0(sK3)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f101,plain,(
% 3.54/1.00    v2_pre_topc(sK0)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f4,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f26,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f4])).
% 3.54/1.00  
% 3.54/1.00  fof(f27,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f26])).
% 3.54/1.00  
% 3.54/1.00  fof(f73,plain,(
% 3.54/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f27])).
% 3.54/1.00  
% 3.54/1.00  fof(f100,plain,(
% 3.54/1.00    ~v2_struct_0(sK0)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f117,plain,(
% 3.54/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f116,plain,(
% 3.54/1.00    sK5 = sK6),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f17,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f46,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f17])).
% 3.54/1.00  
% 3.54/1.00  fof(f47,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f46])).
% 3.54/1.00  
% 3.54/1.00  fof(f59,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(nnf_transformation,[],[f47])).
% 3.54/1.00  
% 3.54/1.00  fof(f60,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f59])).
% 3.54/1.00  
% 3.54/1.00  fof(f93,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f60])).
% 3.54/1.00  
% 3.54/1.00  fof(f120,plain,(
% 3.54/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(equality_resolution,[],[f93])).
% 3.54/1.00  
% 3.54/1.00  fof(f18,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f48,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f18])).
% 3.54/1.00  
% 3.54/1.00  fof(f95,plain,(
% 3.54/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f48])).
% 3.54/1.00  
% 3.54/1.00  fof(f20,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f50,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f20])).
% 3.54/1.00  
% 3.54/1.00  fof(f51,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f50])).
% 3.54/1.00  
% 3.54/1.00  fof(f61,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(nnf_transformation,[],[f51])).
% 3.54/1.00  
% 3.54/1.00  fof(f98,plain,(
% 3.54/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f61])).
% 3.54/1.00  
% 3.54/1.00  fof(f122,plain,(
% 3.54/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(equality_resolution,[],[f98])).
% 3.54/1.00  
% 3.54/1.00  fof(f11,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f35,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f11])).
% 3.54/1.00  
% 3.54/1.00  fof(f36,plain,(
% 3.54/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.54/1.00    inference(flattening,[],[f35])).
% 3.54/1.00  
% 3.54/1.00  fof(f82,plain,(
% 3.54/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f36])).
% 3.54/1.00  
% 3.54/1.00  fof(f9,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f32,plain,(
% 3.54/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f9])).
% 3.54/1.00  
% 3.54/1.00  fof(f33,plain,(
% 3.54/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f32])).
% 3.54/1.00  
% 3.54/1.00  fof(f78,plain,(
% 3.54/1.00    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f33])).
% 3.54/1.00  
% 3.54/1.00  fof(f3,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f24,plain,(
% 3.54/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f3])).
% 3.54/1.00  
% 3.54/1.00  fof(f25,plain,(
% 3.54/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f24])).
% 3.54/1.00  
% 3.54/1.00  fof(f72,plain,(
% 3.54/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f25])).
% 3.54/1.00  
% 3.54/1.00  fof(f10,axiom,(
% 3.54/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f34,plain,(
% 3.54/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.54/1.00    inference(ennf_transformation,[],[f10])).
% 3.54/1.00  
% 3.54/1.00  fof(f80,plain,(
% 3.54/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.54/1.00    inference(cnf_transformation,[],[f34])).
% 3.54/1.00  
% 3.54/1.00  fof(f8,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f31,plain,(
% 3.54/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f8])).
% 3.54/1.00  
% 3.54/1.00  fof(f77,plain,(
% 3.54/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f31])).
% 3.54/1.00  
% 3.54/1.00  fof(f6,axiom,(
% 3.54/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f29,plain,(
% 3.54/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f6])).
% 3.54/1.00  
% 3.54/1.00  fof(f75,plain,(
% 3.54/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f29])).
% 3.54/1.00  
% 3.54/1.00  fof(f5,axiom,(
% 3.54/1.00    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f28,plain,(
% 3.54/1.00    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.54/1.00    inference(ennf_transformation,[],[f5])).
% 3.54/1.00  
% 3.54/1.00  fof(f74,plain,(
% 3.54/1.00    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f28])).
% 3.54/1.00  
% 3.54/1.00  fof(f14,axiom,(
% 3.54/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.54/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/1.00  
% 3.54/1.00  fof(f40,plain,(
% 3.54/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.54/1.00    inference(ennf_transformation,[],[f14])).
% 3.54/1.00  
% 3.54/1.00  fof(f41,plain,(
% 3.54/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.54/1.00    inference(flattening,[],[f40])).
% 3.54/1.00  
% 3.54/1.00  fof(f89,plain,(
% 3.54/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.54/1.00    inference(cnf_transformation,[],[f41])).
% 3.54/1.00  
% 3.54/1.00  fof(f118,plain,(
% 3.54/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f114,plain,(
% 3.54/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  fof(f106,plain,(
% 3.54/1.00    ~v2_struct_0(sK2)),
% 3.54/1.00    inference(cnf_transformation,[],[f69])).
% 3.54/1.00  
% 3.54/1.00  cnf(c_39,negated_conjecture,
% 3.54/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1862,plain,
% 3.54/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_26,plain,
% 3.54/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1869,plain,
% 3.54/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_35,negated_conjecture,
% 3.54/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.54/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_18,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/1.00      | ~ l1_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_272,plain,
% 3.54/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/1.00      | ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_18,c_6]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_273,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_272]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1852,plain,
% 3.54/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4789,plain,
% 3.54/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) = iProver_top
% 3.54/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_35,c_1852]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_46,negated_conjecture,
% 3.54/1.00      ( l1_pre_topc(sK0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_51,plain,
% 3.54/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_41,negated_conjecture,
% 3.54/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1860,plain,
% 3.54/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1883,plain,
% 3.54/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3475,plain,
% 3.54/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1860,c_1883]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4916,plain,
% 3.54/1.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_4789,c_51,c_3475]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4917,plain,
% 3.54/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_4916]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4924,plain,
% 3.54/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.54/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1869,c_4917]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5177,plain,
% 3.54/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_4924,c_51,c_3475]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_21,plain,
% 3.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.54/1.00      | ~ m1_pre_topc(X3,X4)
% 3.54/1.00      | ~ m1_pre_topc(X3,X1)
% 3.54/1.00      | ~ m1_pre_topc(X1,X4)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/1.00      | ~ v1_funct_1(X0)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X4)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X4)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_37,negated_conjecture,
% 3.54/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_644,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ m1_pre_topc(X1,X2)
% 3.54/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.54/1.00      | ~ v1_funct_1(X3)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X4)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X4)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 3.54/1.00      | u1_struct_0(X4) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.54/1.00      | sK4 != X3 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_37]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_645,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ m1_pre_topc(X1,X2)
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/1.00      | ~ v1_funct_1(sK4)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X3)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ v2_pre_topc(X3)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.54/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_644]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_38,negated_conjecture,
% 3.54/1.00      ( v1_funct_1(sK4) ),
% 3.54/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_649,plain,
% 3.54/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/1.00      | ~ m1_pre_topc(X1,X2)
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X3)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ v2_pre_topc(X3)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.54/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_645,c_38]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_650,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ m1_pre_topc(X1,X2)
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X3)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ v2_pre_topc(X3)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.54/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_649]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_29,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X2,X0)
% 3.54/1.00      | m1_pre_topc(X2,X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_681,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_pre_topc(X1,X2)
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X3)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ v2_pre_topc(X3)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 3.54/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(forward_subsumption_resolution,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_650,c_29]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1850,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,X3) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X3) = iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X3) != iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X3) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3197,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,sK1,X0,X1,sK4)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X2) = iProver_top
% 3.54/1.00      | v2_struct_0(sK1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X2) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X2) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.54/1.00      inference(equality_resolution,[status(thm)],[c_1850]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_45,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_52,plain,
% 3.54/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_44,negated_conjecture,
% 3.54/1.00      ( v2_pre_topc(sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_53,plain,
% 3.54/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_43,negated_conjecture,
% 3.54/1.00      ( l1_pre_topc(sK1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_54,plain,
% 3.54/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3915,plain,
% 3.54/1.00      ( l1_pre_topc(X2) != iProver_top
% 3.54/1.00      | v2_struct_0(X2) = iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,sK1,X0,X1,sK4)
% 3.54/1.00      | v2_pre_topc(X2) != iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3197,c_52,c_53,c_54]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3916,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,sK1,X0,X1,sK4)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X2) = iProver_top
% 3.54/1.00      | v2_pre_topc(X2) != iProver_top
% 3.54/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_3915]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3927,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(equality_resolution,[status(thm)],[c_3916]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_36,negated_conjecture,
% 3.54/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_61,plain,
% 3.54/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5999,plain,
% 3.54/1.00      ( m1_pre_topc(sK3,X1) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3927,c_61]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6000,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_5999]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6012,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK3,sK2,sK4)
% 3.54/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_5177,c_6000]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_20,plain,
% 3.54/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.54/1.00      | ~ m1_pre_topc(X3,X1)
% 3.54/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/1.00      | ~ v1_funct_1(X0)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.54/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_695,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.54/1.00      | ~ v1_funct_1(X2)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X3)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X3)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.54/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.54/1.00      | sK4 != X2 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_37]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_696,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/1.00      | ~ v1_funct_1(sK4)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 3.54/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_695]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_700,plain,
% 3.54/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/1.00      | ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 3.54/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_696,c_38]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_701,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 3.54/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_700]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1849,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3042,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k2_tmap_1(X0,sK1,sK4,X1)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(sK1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.54/1.00      inference(equality_resolution,[status(thm)],[c_1849]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3733,plain,
% 3.54/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k2_tmap_1(X0,sK1,sK4,X1)
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3042,c_52,c_53,c_54]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3734,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),sK4,u1_struct_0(X1)) = k2_tmap_1(X0,sK1,sK4,X1)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_3733]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3744,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(sK3) = iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(equality_resolution,[status(thm)],[c_3734]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_40,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK3) ),
% 3.54/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_57,plain,
% 3.54/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3474,plain,
% 3.54/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1862,c_1883]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3865,plain,
% 3.54/1.00      ( v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3744,c_51,c_57,c_61,c_3474]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3866,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_3865]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5183,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_5177,c_3866]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_47,negated_conjecture,
% 3.54/1.00      ( v2_pre_topc(sK0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_50,plain,
% 3.54/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_58,plain,
% 3.54/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | v2_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3224,plain,
% 3.54/1.00      ( ~ m1_pre_topc(sK3,X0)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4173,plain,
% 3.54/1.00      ( ~ m1_pre_topc(sK3,sK0)
% 3.54/1.00      | ~ v2_pre_topc(sK0)
% 3.54/1.00      | v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(sK0) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_3224]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4174,plain,
% 3.54/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) = iProver_top
% 3.54/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_4173]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5249,plain,
% 3.54/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_5183,c_50,c_51,c_58,c_4174]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6018,plain,
% 3.54/1.00      ( k3_tmap_1(X0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 3.54/1.00      | m1_pre_topc(sK3,X0) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_6012,c_5249]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_9376,plain,
% 3.54/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 3.54/1.00      | v2_struct_0(sK0) = iProver_top
% 3.54/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1862,c_6018]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_48,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_49,plain,
% 3.54/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10178,plain,
% 3.54/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_9376,c_49,c_50,c_51]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_31,negated_conjecture,
% 3.54/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.54/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1866,plain,
% 3.54/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_32,negated_conjecture,
% 3.54/1.00      ( sK5 = sK6 ),
% 3.54/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1933,plain,
% 3.54/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_1866,c_32]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10181,plain,
% 3.54/1.00      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) = iProver_top ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_10178,c_1933]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_23,plain,
% 3.54/1.00      ( v1_tsep_1(X0,X1)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/1.00      | ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_25,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_262,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/1.00      | v1_tsep_1(X0,X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_23,c_25]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_263,plain,
% 3.54/1.00      ( v1_tsep_1(X0,X1)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.54/1.00      | ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_262]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_27,plain,
% 3.54/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/1.00      | ~ v1_tsep_1(X4,X0)
% 3.54/1.00      | ~ m1_pre_topc(X4,X0)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/1.00      | ~ v1_funct_1(X2)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_588,plain,
% 3.54/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X5),X6)
% 3.54/1.00      | ~ m1_pre_topc(X5,X6)
% 3.54/1.00      | ~ m1_pre_topc(X4,X0)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/1.00      | ~ v1_funct_1(X2)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | ~ v2_pre_topc(X6)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X6)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X0)
% 3.54/1.00      | X4 != X5
% 3.54/1.00      | X0 != X6 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_263,c_27]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_589,plain,
% 3.54/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X4),X0)
% 3.54/1.00      | ~ m1_pre_topc(X4,X0)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/1.00      | ~ v1_funct_1(X2)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_12,plain,
% 3.54/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.54/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_625,plain,
% 3.54/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X4),X0)
% 3.54/1.00      | ~ m1_pre_topc(X4,X0)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/1.00      | ~ v1_funct_1(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1) ),
% 3.54/1.00      inference(forward_subsumption_resolution,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_589,c_12]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_740,plain,
% 3.54/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.54/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X4),X0)
% 3.54/1.00      | ~ m1_pre_topc(X4,X0)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.54/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.54/1.00      | ~ v1_funct_1(X2)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X4)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.54/1.00      | sK4 != X2 ),
% 3.54/1.00      inference(resolution_lifted,[status(thm)],[c_625,c_37]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_741,plain,
% 3.54/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.54/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X2)
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.54/1.00      | ~ v1_funct_1(sK4)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(unflattening,[status(thm)],[c_740]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_745,plain,
% 3.54/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X2)
% 3.54/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.54/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_741,c_38]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_746,plain,
% 3.54/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.54/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X2)
% 3.54/1.00      | ~ m1_pre_topc(X0,X2)
% 3.54/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(X2)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(X2)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(X2)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_745]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1848,plain,
% 3.54/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.54/1.00      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) != iProver_top
% 3.54/1.00      | r1_tmap_1(X1,X0,sK4,X3) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X2),X1) != iProver_top
% 3.54/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.54/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(X2) = iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3180,plain,
% 3.54/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.54/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(sK3) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(equality_resolution,[status(thm)],[c_1848]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1141,plain,( X0 = X0 ),theory(equality) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2274,plain,
% 3.54/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2565,plain,
% 3.54/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK3,X1,sK4,X0),X2)
% 3.54/1.00      | r1_tmap_1(sK3,X1,sK4,X2)
% 3.54/1.00      | ~ v3_pre_topc(u1_struct_0(X0),sK3)
% 3.54/1.00      | ~ m1_pre_topc(X0,sK3)
% 3.54/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.54/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 3.54/1.00      | v2_struct_0(X0)
% 3.54/1.00      | v2_struct_0(X1)
% 3.54/1.00      | v2_struct_0(sK3)
% 3.54/1.00      | ~ v2_pre_topc(X1)
% 3.54/1.00      | ~ v2_pre_topc(sK3)
% 3.54/1.00      | ~ l1_pre_topc(X1)
% 3.54/1.00      | ~ l1_pre_topc(sK3)
% 3.54/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_746]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2566,plain,
% 3.54/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.54/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.54/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_struct_0(sK3) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_2565]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3842,plain,
% 3.54/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.54/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3180,c_51,c_57,c_2274,c_2566,c_3474]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3843,plain,
% 3.54/1.00      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.54/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK3,X0,sK4,X1),X2) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X1),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X1) = iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_3842]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3860,plain,
% 3.54/1.00      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.54/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top
% 3.54/1.00      | v2_struct_0(sK1) = iProver_top
% 3.54/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 3.54/1.00      inference(equality_resolution,[status(thm)],[c_3843]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5383,plain,
% 3.54/1.00      ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.54/1.00      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3860,c_50,c_51,c_52,c_53,c_54,c_58,c_61,c_4174]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5384,plain,
% 3.54/1.00      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
% 3.54/1.00      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.54/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_5383]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10185,plain,
% 3.54/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.54/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_10181,c_5384]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1884,plain,
% 3.54/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.54/1.00      | v2_pre_topc(X1) != iProver_top
% 3.54/1.00      | v2_pre_topc(X0) = iProver_top
% 3.54/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6182,plain,
% 3.54/1.00      ( v2_pre_topc(sK0) != iProver_top
% 3.54/1.00      | v2_pre_topc(sK2) = iProver_top
% 3.54/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1860,c_1884]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7005,plain,
% 3.54/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_6182,c_50,c_51]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_9,plain,
% 3.54/1.00      ( ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X0)
% 3.54/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1880,plain,
% 3.54/1.00      ( v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4212,plain,
% 3.54/1.00      ( v2_pre_topc(sK2) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.54/1.00      | v1_pre_topc(sK3) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_35,c_1880]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4215,plain,
% 3.54/1.00      ( v2_pre_topc(sK2) != iProver_top
% 3.54/1.00      | v1_pre_topc(sK3) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_4212,c_51,c_3475]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7010,plain,
% 3.54/1.00      ( v1_pre_topc(sK3) = iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_7005,c_4215]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3601,plain,
% 3.54/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_3474,c_51]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2,plain,
% 3.54/1.00      ( ~ l1_pre_topc(X0)
% 3.54/1.00      | ~ v1_pre_topc(X0)
% 3.54/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.54/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1885,plain,
% 3.54/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top
% 3.54/1.00      | v1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4075,plain,
% 3.54/1.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 3.54/1.00      | v1_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_3601,c_1885]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7014,plain,
% 3.54/1.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_7010,c_4075]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_11,plain,
% 3.54/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.54/1.00      | X2 = X1
% 3.54/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1878,plain,
% 3.54/1.00      ( X0 = X1
% 3.54/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.54/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5513,plain,
% 3.54/1.00      ( g1_pre_topc(X0,X1) != sK3
% 3.54/1.00      | u1_struct_0(sK2) = X0
% 3.54/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_35,c_1878]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7,plain,
% 3.54/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.54/1.00      | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3683,plain,
% 3.54/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.54/1.00      | ~ l1_pre_topc(sK2) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3688,plain,
% 3.54/1.00      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.54/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_3683]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5514,plain,
% 3.54/1.00      ( g1_pre_topc(X0,X1) != sK3
% 3.54/1.00      | u1_struct_0(sK2) = X0
% 3.54/1.00      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_35,c_1878]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5652,plain,
% 3.54/1.00      ( u1_struct_0(sK2) = X0 | g1_pre_topc(X0,X1) != sK3 ),
% 3.54/1.00      inference(global_propositional_subsumption,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_5513,c_51,c_3475,c_3688,c_5514]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5653,plain,
% 3.54/1.00      ( g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0 ),
% 3.54/1.00      inference(renaming,[status(thm)],[c_5652]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_7094,plain,
% 3.54/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_7014,c_5653]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10186,plain,
% 3.54/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.54/1.00      | v3_pre_topc(u1_struct_0(sK3),sK3) != iProver_top
% 3.54/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.54/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.54/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_10185,c_7094]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_5,plain,
% 3.54/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4,plain,
% 3.54/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_497,plain,
% 3.54/1.00      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.54/1.00      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1851,plain,
% 3.54/1.00      ( k2_struct_0(X0) = u1_struct_0(X0)
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3978,plain,
% 3.54/1.00      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_3601,c_1851]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_19,plain,
% 3.54/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.54/1.00      | ~ v2_pre_topc(X0)
% 3.54/1.00      | ~ l1_pre_topc(X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1871,plain,
% 3.54/1.00      ( v3_pre_topc(k2_struct_0(X0),X0) = iProver_top
% 3.54/1.00      | v2_pre_topc(X0) != iProver_top
% 3.54/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4677,plain,
% 3.54/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK3) = iProver_top
% 3.54/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.54/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_3978,c_1871]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_30,negated_conjecture,
% 3.54/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.54/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_65,plain,
% 3.54/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_34,negated_conjecture,
% 3.54/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.54/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_62,plain,
% 3.54/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_42,negated_conjecture,
% 3.54/1.00      ( ~ v2_struct_0(sK2) ),
% 3.54/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_55,plain,
% 3.54/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.54/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(contradiction,plain,
% 3.54/1.00      ( $false ),
% 3.54/1.00      inference(minisat,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_10186,c_4924,c_4677,c_4174,c_3475,c_3474,c_65,c_62,
% 3.54/1.00                 c_58,c_55,c_51,c_50]) ).
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  ------                               Statistics
% 3.54/1.00  
% 3.54/1.00  ------ General
% 3.54/1.00  
% 3.54/1.00  abstr_ref_over_cycles:                  0
% 3.54/1.00  abstr_ref_under_cycles:                 0
% 3.54/1.00  gc_basic_clause_elim:                   0
% 3.54/1.00  forced_gc_time:                         0
% 3.54/1.00  parsing_time:                           0.011
% 3.54/1.00  unif_index_cands_time:                  0.
% 3.54/1.00  unif_index_add_time:                    0.
% 3.54/1.00  orderings_time:                         0.
% 3.54/1.00  out_proof_time:                         0.017
% 3.54/1.00  total_time:                             0.326
% 3.54/1.00  num_of_symbols:                         60
% 3.54/1.00  num_of_terms:                           9331
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing
% 3.54/1.00  
% 3.54/1.00  num_of_splits:                          0
% 3.54/1.00  num_of_split_atoms:                     0
% 3.54/1.00  num_of_reused_defs:                     0
% 3.54/1.00  num_eq_ax_congr_red:                    20
% 3.54/1.00  num_of_sem_filtered_clauses:            1
% 3.54/1.00  num_of_subtypes:                        0
% 3.54/1.00  monotx_restored_types:                  0
% 3.54/1.00  sat_num_of_epr_types:                   0
% 3.54/1.00  sat_num_of_non_cyclic_types:            0
% 3.54/1.00  sat_guarded_non_collapsed_types:        0
% 3.54/1.00  num_pure_diseq_elim:                    0
% 3.54/1.00  simp_replaced_by:                       0
% 3.54/1.00  res_preprocessed:                       214
% 3.54/1.00  prep_upred:                             0
% 3.54/1.00  prep_unflattend:                        10
% 3.54/1.00  smt_new_axioms:                         0
% 3.54/1.00  pred_elim_cands:                        8
% 3.54/1.00  pred_elim:                              4
% 3.54/1.00  pred_elim_cl:                           5
% 3.54/1.00  pred_elim_cycles:                       7
% 3.54/1.00  merged_defs:                            0
% 3.54/1.00  merged_defs_ncl:                        0
% 3.54/1.00  bin_hyper_res:                          0
% 3.54/1.00  prep_cycles:                            4
% 3.54/1.00  pred_elim_time:                         0.027
% 3.54/1.00  splitting_time:                         0.
% 3.54/1.00  sem_filter_time:                        0.
% 3.54/1.00  monotx_time:                            0.001
% 3.54/1.00  subtype_inf_time:                       0.
% 3.54/1.00  
% 3.54/1.00  ------ Problem properties
% 3.54/1.00  
% 3.54/1.00  clauses:                                43
% 3.54/1.00  conjectures:                            17
% 3.54/1.00  epr:                                    16
% 3.54/1.00  horn:                                   38
% 3.54/1.00  ground:                                 17
% 3.54/1.00  unary:                                  19
% 3.54/1.00  binary:                                 3
% 3.54/1.00  lits:                                   144
% 3.54/1.00  lits_eq:                                19
% 3.54/1.00  fd_pure:                                0
% 3.54/1.00  fd_pseudo:                              0
% 3.54/1.00  fd_cond:                                0
% 3.54/1.00  fd_pseudo_cond:                         2
% 3.54/1.00  ac_symbols:                             0
% 3.54/1.00  
% 3.54/1.00  ------ Propositional Solver
% 3.54/1.00  
% 3.54/1.00  prop_solver_calls:                      28
% 3.54/1.00  prop_fast_solver_calls:                 2102
% 3.54/1.00  smt_solver_calls:                       0
% 3.54/1.00  smt_fast_solver_calls:                  0
% 3.54/1.00  prop_num_of_clauses:                    3772
% 3.54/1.00  prop_preprocess_simplified:             10905
% 3.54/1.00  prop_fo_subsumed:                       79
% 3.54/1.00  prop_solver_time:                       0.
% 3.54/1.00  smt_solver_time:                        0.
% 3.54/1.00  smt_fast_solver_time:                   0.
% 3.54/1.00  prop_fast_solver_time:                  0.
% 3.54/1.00  prop_unsat_core_time:                   0.
% 3.54/1.00  
% 3.54/1.00  ------ QBF
% 3.54/1.00  
% 3.54/1.00  qbf_q_res:                              0
% 3.54/1.00  qbf_num_tautologies:                    0
% 3.54/1.00  qbf_prep_cycles:                        0
% 3.54/1.00  
% 3.54/1.00  ------ BMC1
% 3.54/1.00  
% 3.54/1.00  bmc1_current_bound:                     -1
% 3.54/1.00  bmc1_last_solved_bound:                 -1
% 3.54/1.00  bmc1_unsat_core_size:                   -1
% 3.54/1.00  bmc1_unsat_core_parents_size:           -1
% 3.54/1.00  bmc1_merge_next_fun:                    0
% 3.54/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.54/1.00  
% 3.54/1.00  ------ Instantiation
% 3.54/1.00  
% 3.54/1.00  inst_num_of_clauses:                    1070
% 3.54/1.00  inst_num_in_passive:                    558
% 3.54/1.00  inst_num_in_active:                     497
% 3.54/1.00  inst_num_in_unprocessed:                15
% 3.54/1.00  inst_num_of_loops:                      520
% 3.54/1.00  inst_num_of_learning_restarts:          0
% 3.54/1.00  inst_num_moves_active_passive:          21
% 3.54/1.00  inst_lit_activity:                      0
% 3.54/1.00  inst_lit_activity_moves:                0
% 3.54/1.00  inst_num_tautologies:                   0
% 3.54/1.00  inst_num_prop_implied:                  0
% 3.54/1.00  inst_num_existing_simplified:           0
% 3.54/1.00  inst_num_eq_res_simplified:             0
% 3.54/1.00  inst_num_child_elim:                    0
% 3.54/1.00  inst_num_of_dismatching_blockings:      546
% 3.54/1.00  inst_num_of_non_proper_insts:           1407
% 3.54/1.00  inst_num_of_duplicates:                 0
% 3.54/1.00  inst_inst_num_from_inst_to_res:         0
% 3.54/1.00  inst_dismatching_checking_time:         0.
% 3.54/1.00  
% 3.54/1.00  ------ Resolution
% 3.54/1.00  
% 3.54/1.00  res_num_of_clauses:                     0
% 3.54/1.00  res_num_in_passive:                     0
% 3.54/1.00  res_num_in_active:                      0
% 3.54/1.00  res_num_of_loops:                       218
% 3.54/1.00  res_forward_subset_subsumed:            82
% 3.54/1.00  res_backward_subset_subsumed:           2
% 3.54/1.00  res_forward_subsumed:                   0
% 3.54/1.00  res_backward_subsumed:                  0
% 3.54/1.00  res_forward_subsumption_resolution:     3
% 3.54/1.00  res_backward_subsumption_resolution:    0
% 3.54/1.00  res_clause_to_clause_subsumption:       566
% 3.54/1.00  res_orphan_elimination:                 0
% 3.54/1.00  res_tautology_del:                      104
% 3.54/1.00  res_num_eq_res_simplified:              0
% 3.54/1.00  res_num_sel_changes:                    0
% 3.54/1.00  res_moves_from_active_to_pass:          0
% 3.54/1.00  
% 3.54/1.00  ------ Superposition
% 3.54/1.00  
% 3.54/1.00  sup_time_total:                         0.
% 3.54/1.00  sup_time_generating:                    0.
% 3.54/1.00  sup_time_sim_full:                      0.
% 3.54/1.00  sup_time_sim_immed:                     0.
% 3.54/1.00  
% 3.54/1.00  sup_num_of_clauses:                     141
% 3.54/1.00  sup_num_in_active:                      92
% 3.54/1.00  sup_num_in_passive:                     49
% 3.54/1.00  sup_num_of_loops:                       103
% 3.54/1.00  sup_fw_superposition:                   85
% 3.54/1.00  sup_bw_superposition:                   85
% 3.54/1.00  sup_immediate_simplified:               56
% 3.54/1.00  sup_given_eliminated:                   0
% 3.54/1.00  comparisons_done:                       0
% 3.54/1.00  comparisons_avoided:                    0
% 3.54/1.00  
% 3.54/1.00  ------ Simplifications
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  sim_fw_subset_subsumed:                 22
% 3.54/1.00  sim_bw_subset_subsumed:                 11
% 3.54/1.00  sim_fw_subsumed:                        5
% 3.54/1.00  sim_bw_subsumed:                        0
% 3.54/1.00  sim_fw_subsumption_res:                 0
% 3.54/1.00  sim_bw_subsumption_res:                 0
% 3.54/1.00  sim_tautology_del:                      22
% 3.54/1.00  sim_eq_tautology_del:                   6
% 3.54/1.00  sim_eq_res_simp:                        0
% 3.54/1.00  sim_fw_demodulated:                     0
% 3.54/1.00  sim_bw_demodulated:                     11
% 3.54/1.00  sim_light_normalised:                   37
% 3.54/1.00  sim_joinable_taut:                      0
% 3.54/1.00  sim_joinable_simp:                      0
% 3.54/1.00  sim_ac_normalised:                      0
% 3.54/1.00  sim_smt_subsumption:                    0
% 3.54/1.00  
%------------------------------------------------------------------------------
