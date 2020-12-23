%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:31 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  296 (12167 expanded)
%              Number of clauses        :  183 (3172 expanded)
%              Number of leaves         :   30 (4876 expanded)
%              Depth                    :   29
%              Number of atoms          : 1562 (145430 expanded)
%              Number of equality atoms :  497 (22133 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f69,plain,(
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

fof(f68,plain,(
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

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f64,plain,(
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

fof(f63,plain,
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

fof(f70,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f52,f69,f68,f67,f66,f65,f64,f63])).

fof(f109,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f111,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f115,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f70])).

fof(f103,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f88,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
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

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f113,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

fof(f112,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f105,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f106,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f107,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f114,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

fof(f102,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f12,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f119,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f70])).

fof(f118,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f70])).

fof(f14,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

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

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f126,plain,(
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
    inference(equality_resolution,[],[f100])).

fof(f7,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

fof(f108,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_9904,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_42,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_9892,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9913,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10991,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9892,c_9913])).

cnf(c_47,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_52,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_57,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_10429,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10430,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10429])).

cnf(c_11402,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10991,c_52,c_57,c_10430])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_607,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_9875,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_11407,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_11402,c_9875])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_281,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_8])).

cnf(c_282,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_9884,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_11621,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11407,c_9884])).

cnf(c_19523,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11621,c_52,c_57,c_10430])).

cnf(c_19524,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_19523])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_9917,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9916,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9908,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12240,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11407,c_9908])).

cnf(c_40,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_9894,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_10990,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9894,c_9913])).

cnf(c_59,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_10386,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10387,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10386])).

cnf(c_11357,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10990,c_52,c_59,c_10387])).

cnf(c_11362,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_11357,c_9875])).

cnf(c_36,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_11560,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_11407,c_36])).

cnf(c_12293,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12240,c_11362,c_11407,c_11560])).

cnf(c_48,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_51,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10427,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10434,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10427])).

cnf(c_12536,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12293,c_51,c_52,c_57,c_10430,c_10434])).

cnf(c_12545,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9916,c_12536])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15467,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12545,c_9915])).

cnf(c_17168,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9917,c_15467])).

cnf(c_17,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_12549,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_12556,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12549])).

cnf(c_17877,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17168,c_51,c_52,c_57,c_10430,c_10434,c_12556])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9918,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_17882,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17877,c_9918])).

cnf(c_10,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9911,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11826,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11407,c_9911])).

cnf(c_11851,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11826,c_11560])).

cnf(c_11946,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11851,c_52,c_57,c_10430])).

cnf(c_11947,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_11946])).

cnf(c_11954,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9904,c_11947])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_9903,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11567,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11407,c_9903])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_9902,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_9900,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10100,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9902,c_9900])).

cnf(c_13243,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9892,c_10100])).

cnf(c_13258,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13243,c_11407])).

cnf(c_14014,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11567,c_51,c_52,c_13258])).

cnf(c_14015,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14014])).

cnf(c_14026,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14015,c_9918])).

cnf(c_16450,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK2)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11362,c_14026])).

cnf(c_16464,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16450,c_11362])).

cnf(c_17926,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17882,c_51,c_52,c_57,c_59,c_10387,c_10430,c_10434,c_11954,c_12556,c_16464,c_17168])).

cnf(c_17956,plain,
    ( g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_17926,c_11560])).

cnf(c_19529,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19524,c_17926,c_17956])).

cnf(c_19535,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9904,c_19529])).

cnf(c_19585,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19535,c_52,c_57,c_10430])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_846,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_847,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_851,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_847,c_39])).

cnf(c_852,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_851])).

cnf(c_883,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_852,c_30])).

cnf(c_9872,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_883])).

cnf(c_10561,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK3,X1,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9872])).

cnf(c_10963,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10561])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_53,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_54,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_55,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_62,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_136,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_140,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1305,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1321,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_10522,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_10523,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10522])).

cnf(c_1297,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_12985,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_14346,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10963,c_53,c_54,c_55,c_62,c_136,c_140,c_1321,c_10523,c_12985])).

cnf(c_14347,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_14346])).

cnf(c_9890,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_10979,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_9890,c_9875])).

cnf(c_14352,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14347,c_10979,c_11362])).

cnf(c_14364,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9894,c_14352])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_50,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_14709,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14364,c_50,c_51,c_52])).

cnf(c_14710,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_14709])).

cnf(c_19594,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
    inference(superposition,[status(thm)],[c_19585,c_14710])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_897,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_898,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_902,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_39])).

cnf(c_903,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_902])).

cnf(c_9871,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_10417,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9871])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_58,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10384,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10391,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10384])).

cnf(c_10528,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10417,c_51,c_52,c_58,c_59,c_10387,c_10391])).

cnf(c_10529,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10528])).

cnf(c_10541,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10529])).

cnf(c_10820,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10541,c_53,c_54,c_55,c_62])).

cnf(c_11039,plain,
    ( k2_partfun1(u1_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10979,c_10820])).

cnf(c_13188,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11039,c_11362])).

cnf(c_19595,plain,
    ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_19585,c_13188])).

cnf(c_19602,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19594,c_19595])).

cnf(c_32,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_9898,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_9965,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9898,c_33])).

cnf(c_20643,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19602,c_9965])).

cnf(c_21,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_271,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_23])).

cnf(c_272,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_28,plain,
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_676,plain,
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
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | X4 != X5
    | X0 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_28])).

cnf(c_677,plain,
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
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_713,plain,
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
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_677,c_9])).

cnf(c_732,plain,
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
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_713,c_38])).

cnf(c_733,plain,
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
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(u1_struct_0(X0),X2)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_39])).

cnf(c_738,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ v3_pre_topc(u1_struct_0(X0),X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_9874,plain,
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
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_10518,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k2_tmap_1(X0,sK1,sK4,X1),X2) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9874])).

cnf(c_10798,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X2) = iProver_top
    | r1_tmap_1(X1,sK1,k2_tmap_1(X0,sK1,sK4,X1),X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10518,c_53,c_54,c_55])).

cnf(c_10799,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k2_tmap_1(X0,sK1,sK4,X1),X2) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X2) = iProver_top
    | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10798])).

cnf(c_10813,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10799])).

cnf(c_10906,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10813,c_51,c_52,c_58,c_59,c_62,c_10387,c_10391])).

cnf(c_10907,plain,
    ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10906])).

cnf(c_20685,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20643,c_10907])).

cnf(c_17957,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_17926,c_11407])).

cnf(c_20686,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20685,c_17957])).

cnf(c_12148,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_12155,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12148])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_9896,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11489,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11362,c_9896])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_66,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_56,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20686,c_19535,c_12155,c_11489,c_10430,c_10391,c_10387,c_66,c_59,c_57,c_56,c_52,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 42
% 7.73/1.49  conjectures                             17
% 7.73/1.49  EPR                                     18
% 7.73/1.49  Horn                                    37
% 7.73/1.49  unary                                   18
% 7.73/1.49  binary                                  4
% 7.73/1.49  lits                                    147
% 7.73/1.49  lits eq                                 14
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 0
% 7.73/1.49  fd_pseudo_cond                          1
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Input Options Time Limit: Unbounded
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS status Theorem for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  fof(f16,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f43,plain,(
% 7.73/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f16])).
% 7.73/1.49  
% 7.73/1.49  fof(f95,plain,(
% 7.73/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f43])).
% 7.73/1.49  
% 7.73/1.49  fof(f21,conjecture,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f22,negated_conjecture,(
% 7.73/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.73/1.49    inference(negated_conjecture,[],[f21])).
% 7.73/1.49  
% 7.73/1.49  fof(f51,plain,(
% 7.73/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f22])).
% 7.73/1.49  
% 7.73/1.49  fof(f52,plain,(
% 7.73/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f51])).
% 7.73/1.49  
% 7.73/1.49  fof(f69,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f68,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f67,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f66,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f65,plain,(
% 7.73/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f64,plain,(
% 7.73/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f63,plain,(
% 7.73/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f70,plain,(
% 7.73/1.49    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f52,f69,f68,f67,f66,f65,f64,f63])).
% 7.73/1.49  
% 7.73/1.49  fof(f109,plain,(
% 7.73/1.49    m1_pre_topc(sK2,sK0)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f6,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f27,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f6])).
% 7.73/1.49  
% 7.73/1.49  fof(f79,plain,(
% 7.73/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f27])).
% 7.73/1.49  
% 7.73/1.49  fof(f104,plain,(
% 7.73/1.49    l1_pre_topc(sK0)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f5,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f26,plain,(
% 7.73/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f5])).
% 7.73/1.49  
% 7.73/1.49  fof(f78,plain,(
% 7.73/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f26])).
% 7.73/1.49  
% 7.73/1.49  fof(f4,axiom,(
% 7.73/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f25,plain,(
% 7.73/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f4])).
% 7.73/1.49  
% 7.73/1.49  fof(f77,plain,(
% 7.73/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f25])).
% 7.73/1.49  
% 7.73/1.49  fof(f10,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f33,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f10])).
% 7.73/1.49  
% 7.73/1.49  fof(f58,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f33])).
% 7.73/1.49  
% 7.73/1.49  fof(f86,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f58])).
% 7.73/1.49  
% 7.73/1.49  fof(f1,axiom,(
% 7.73/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f53,plain,(
% 7.73/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.49    inference(nnf_transformation,[],[f1])).
% 7.73/1.49  
% 7.73/1.49  fof(f54,plain,(
% 7.73/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.49    inference(flattening,[],[f53])).
% 7.73/1.49  
% 7.73/1.49  fof(f71,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.73/1.49    inference(cnf_transformation,[],[f54])).
% 7.73/1.49  
% 7.73/1.49  fof(f122,plain,(
% 7.73/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.73/1.49    inference(equality_resolution,[],[f71])).
% 7.73/1.49  
% 7.73/1.49  fof(f2,axiom,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f55,plain,(
% 7.73/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.73/1.49    inference(nnf_transformation,[],[f2])).
% 7.73/1.49  
% 7.73/1.49  fof(f75,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f55])).
% 7.73/1.49  
% 7.73/1.49  fof(f9,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f31,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f9])).
% 7.73/1.49  
% 7.73/1.49  fof(f32,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f31])).
% 7.73/1.49  
% 7.73/1.49  fof(f56,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f32])).
% 7.73/1.49  
% 7.73/1.49  fof(f57,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f56])).
% 7.73/1.49  
% 7.73/1.49  fof(f83,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f57])).
% 7.73/1.49  
% 7.73/1.49  fof(f111,plain,(
% 7.73/1.49    m1_pre_topc(sK3,sK0)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f115,plain,(
% 7.73/1.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f103,plain,(
% 7.73/1.49    v2_pre_topc(sK0)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f3,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f23,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f3])).
% 7.73/1.49  
% 7.73/1.49  fof(f24,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f23])).
% 7.73/1.49  
% 7.73/1.49  fof(f76,plain,(
% 7.73/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f24])).
% 7.73/1.49  
% 7.73/1.49  fof(f74,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f55])).
% 7.73/1.49  
% 7.73/1.49  fof(f11,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f34,plain,(
% 7.73/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f11])).
% 7.73/1.49  
% 7.73/1.49  fof(f35,plain,(
% 7.73/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f34])).
% 7.73/1.49  
% 7.73/1.49  fof(f88,plain,(
% 7.73/1.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f35])).
% 7.73/1.49  
% 7.73/1.49  fof(f73,plain,(
% 7.73/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f54])).
% 7.73/1.49  
% 7.73/1.49  fof(f8,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f30,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f8])).
% 7.73/1.49  
% 7.73/1.49  fof(f81,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f30])).
% 7.73/1.49  
% 7.73/1.49  fof(f17,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f44,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f17])).
% 7.73/1.49  
% 7.73/1.49  fof(f96,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f44])).
% 7.73/1.49  
% 7.73/1.49  fof(f18,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f45,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f18])).
% 7.73/1.49  
% 7.73/1.49  fof(f46,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f45])).
% 7.73/1.49  
% 7.73/1.49  fof(f61,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f46])).
% 7.73/1.49  
% 7.73/1.49  fof(f98,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f61])).
% 7.73/1.49  
% 7.73/1.49  fof(f20,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f49,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f20])).
% 7.73/1.49  
% 7.73/1.49  fof(f50,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f49])).
% 7.73/1.49  
% 7.73/1.49  fof(f101,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f13,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f38,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f13])).
% 7.73/1.49  
% 7.73/1.49  fof(f39,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f38])).
% 7.73/1.49  
% 7.73/1.49  fof(f90,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f39])).
% 7.73/1.49  
% 7.73/1.49  fof(f113,plain,(
% 7.73/1.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f112,plain,(
% 7.73/1.49    v1_funct_1(sK4)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f105,plain,(
% 7.73/1.49    ~v2_struct_0(sK1)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f106,plain,(
% 7.73/1.49    v2_pre_topc(sK1)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f107,plain,(
% 7.73/1.49    l1_pre_topc(sK1)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f114,plain,(
% 7.73/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f102,plain,(
% 7.73/1.49    ~v2_struct_0(sK0)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f12,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f36,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f12])).
% 7.73/1.49  
% 7.73/1.49  fof(f37,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f89,plain,(
% 7.73/1.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f110,plain,(
% 7.73/1.49    ~v2_struct_0(sK3)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f119,plain,(
% 7.73/1.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f118,plain,(
% 7.73/1.49    sK5 = sK6),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f14,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f40,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f14])).
% 7.73/1.49  
% 7.73/1.49  fof(f41,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f40])).
% 7.73/1.49  
% 7.73/1.49  fof(f59,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f41])).
% 7.73/1.49  
% 7.73/1.49  fof(f60,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f59])).
% 7.73/1.49  
% 7.73/1.49  fof(f92,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f60])).
% 7.73/1.49  
% 7.73/1.49  fof(f124,plain,(
% 7.73/1.49    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.73/1.49    inference(equality_resolution,[],[f92])).
% 7.73/1.49  
% 7.73/1.49  fof(f15,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f42,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f15])).
% 7.73/1.49  
% 7.73/1.49  fof(f94,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f42])).
% 7.73/1.49  
% 7.73/1.49  fof(f19,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f47,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f19])).
% 7.73/1.49  
% 7.73/1.49  fof(f48,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f47])).
% 7.73/1.49  
% 7.73/1.49  fof(f62,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f48])).
% 7.73/1.49  
% 7.73/1.49  fof(f100,plain,(
% 7.73/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f62])).
% 7.73/1.49  
% 7.73/1.49  fof(f126,plain,(
% 7.73/1.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(equality_resolution,[],[f100])).
% 7.73/1.49  
% 7.73/1.49  fof(f7,axiom,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f28,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f7])).
% 7.73/1.49  
% 7.73/1.49  fof(f29,plain,(
% 7.73/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.73/1.49    inference(flattening,[],[f28])).
% 7.73/1.49  
% 7.73/1.49  fof(f80,plain,(
% 7.73/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f29])).
% 7.73/1.49  
% 7.73/1.49  fof(f116,plain,(
% 7.73/1.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f120,plain,(
% 7.73/1.49    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  fof(f108,plain,(
% 7.73/1.49    ~v2_struct_0(sK2)),
% 7.73/1.49    inference(cnf_transformation,[],[f70])).
% 7.73/1.49  
% 7.73/1.49  cnf(c_24,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9904,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 7.73/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_42,negated_conjecture,
% 7.73/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9892,plain,
% 7.73/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9913,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top
% 7.73/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10991,plain,
% 7.73/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9892,c_9913]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_47,negated_conjecture,
% 7.73/1.49      ( l1_pre_topc(sK0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_52,plain,
% 7.73/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_57,plain,
% 7.73/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10429,plain,
% 7.73/1.49      ( ~ m1_pre_topc(sK2,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10430,plain,
% 7.73/1.49      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_10429]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11402,plain,
% 7.73/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_10991,c_52,c_57,c_10430]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7,plain,
% 7.73/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6,plain,
% 7.73/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_607,plain,
% 7.73/1.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.73/1.49      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9875,plain,
% 7.73/1.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.73/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11407,plain,
% 7.73/1.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11402,c_9875]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_16,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.73/1.49      | ~ l1_pre_topc(X0)
% 7.73/1.49      | ~ l1_pre_topc(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_281,plain,
% 7.73/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.73/1.49      | ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ l1_pre_topc(X1) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_16,c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_282,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.73/1.49      | ~ l1_pre_topc(X1) ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_281]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9884,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11621,plain,
% 7.73/1.49      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11407,c_9884]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19523,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_11621,c_52,c_57,c_10430]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19524,plain,
% 7.73/1.49      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_19523]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2,plain,
% 7.73/1.49      ( r1_tarski(X0,X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f122]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9917,plain,
% 7.73/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9916,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.73/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13,plain,
% 7.73/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 7.73/1.49      | ~ l1_pre_topc(X1)
% 7.73/1.49      | ~ v2_pre_topc(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9908,plain,
% 7.73/1.49      ( v3_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top
% 7.73/1.49      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12240,plain,
% 7.73/1.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))))) = iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11407,c_9908]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_40,negated_conjecture,
% 7.73/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9894,plain,
% 7.73/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10990,plain,
% 7.73/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK3) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9894,c_9913]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_59,plain,
% 7.73/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10386,plain,
% 7.73/1.49      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10387,plain,
% 7.73/1.49      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK3) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_10386]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11357,plain,
% 7.73/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_10990,c_52,c_59,c_10387]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11362,plain,
% 7.73/1.49      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11357,c_9875]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_36,negated_conjecture,
% 7.73/1.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.73/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11560,plain,
% 7.73/1.49      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_11407,c_36]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12293,plain,
% 7.73/1.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_12240,c_11362,c_11407,c_11560]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_48,negated_conjecture,
% 7.73/1.49      ( v2_pre_topc(sK0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_51,plain,
% 7.73/1.49      ( v2_pre_topc(sK0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ l1_pre_topc(X1)
% 7.73/1.49      | ~ v2_pre_topc(X1)
% 7.73/1.49      | v2_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10427,plain,
% 7.73/1.49      ( ~ m1_pre_topc(sK2,sK0)
% 7.73/1.49      | ~ l1_pre_topc(sK0)
% 7.73/1.49      | ~ v2_pre_topc(sK0)
% 7.73/1.49      | v2_pre_topc(sK2) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10434,plain,
% 7.73/1.49      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK0) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_10427]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12536,plain,
% 7.73/1.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_12293,c_51,c_52,c_57,c_10430,c_10434]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12545,plain,
% 7.73/1.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.73/1.49      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9916,c_12536]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9915,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.73/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_15467,plain,
% 7.73/1.49      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
% 7.73/1.49      | r1_tarski(X0,k2_struct_0(sK3)) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_12545,c_9915]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17168,plain,
% 7.73/1.49      ( v3_pre_topc(k2_struct_0(sK2),sK2) != iProver_top
% 7.73/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9917,c_15467]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17,plain,
% 7.73/1.49      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.73/1.49      | ~ l1_pre_topc(X0)
% 7.73/1.49      | ~ v2_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12549,plain,
% 7.73/1.49      ( v3_pre_topc(k2_struct_0(sK2),sK2)
% 7.73/1.49      | ~ l1_pre_topc(sK2)
% 7.73/1.49      | ~ v2_pre_topc(sK2) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_12556,plain,
% 7.73/1.49      ( v3_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_12549]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17877,plain,
% 7.73/1.49      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_17168,c_51,c_52,c_57,c_10430,c_10434,c_12556]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_0,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9918,plain,
% 7.73/1.49      ( X0 = X1
% 7.73/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.73/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17882,plain,
% 7.73/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 7.73/1.49      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_17877,c_9918]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.73/1.49      | ~ l1_pre_topc(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9911,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 7.73/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11826,plain,
% 7.73/1.49      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK2) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11407,c_9911]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11851,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_11826,c_11560]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11946,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_11851,c_52,c_57,c_10430]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11947,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_11946]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11954,plain,
% 7.73/1.49      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9904,c_11947]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_25,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.73/1.49      | ~ l1_pre_topc(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9903,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11567,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11407,c_9903]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_26,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X2,X1)
% 7.73/1.49      | ~ m1_pre_topc(X0,X2)
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.73/1.49      | ~ l1_pre_topc(X1)
% 7.73/1.49      | ~ v2_pre_topc(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9902,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,X2) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top
% 7.73/1.49      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_30,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X2,X0)
% 7.73/1.49      | m1_pre_topc(X2,X1)
% 7.73/1.49      | ~ l1_pre_topc(X1)
% 7.73/1.49      | ~ v2_pre_topc(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9900,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 7.73/1.49      | m1_pre_topc(X2,X1) = iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top
% 7.73/1.49      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10100,plain,
% 7.73/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.73/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top
% 7.73/1.49      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(forward_subsumption_resolution,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_9902,c_9900]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13243,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9892,c_10100]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13258,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK0) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_13243,c_11407]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_14014,plain,
% 7.73/1.49      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_11567,c_51,c_52,c_13258]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_14015,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_14014]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_14026,plain,
% 7.73/1.49      ( u1_struct_0(X0) = k2_struct_0(sK2)
% 7.73/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(k2_struct_0(sK2),u1_struct_0(X0)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_14015,c_9918]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_16450,plain,
% 7.73/1.49      ( u1_struct_0(sK3) = k2_struct_0(sK2)
% 7.73/1.49      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_11362,c_14026]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_16464,plain,
% 7.73/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 7.73/1.49      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.73/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_16450,c_11362]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17926,plain,
% 7.73/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_17882,c_51,c_52,c_57,c_59,c_10387,c_10430,c_10434,
% 7.73/1.49                 c_11954,c_12556,c_16464,c_17168]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17956,plain,
% 7.73/1.49      ( g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK2)) = sK3 ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_17926,c_11560]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19529,plain,
% 7.73/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,sK3) = iProver_top ),
% 7.73/1.49      inference(light_normalisation,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_19524,c_17926,c_17956]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19535,plain,
% 7.73/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_9904,c_19529]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19585,plain,
% 7.73/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_19535,c_52,c_57,c_10430]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_19,plain,
% 7.73/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.73/1.49      | ~ m1_pre_topc(X3,X4)
% 7.73/1.49      | ~ m1_pre_topc(X3,X1)
% 7.73/1.49      | ~ m1_pre_topc(X1,X4)
% 7.73/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.49      | ~ v1_funct_1(X0)
% 7.73/1.49      | v2_struct_0(X4)
% 7.73/1.49      | v2_struct_0(X2)
% 7.73/1.49      | ~ l1_pre_topc(X4)
% 7.73/1.49      | ~ l1_pre_topc(X2)
% 7.73/1.49      | ~ v2_pre_topc(X4)
% 7.73/1.49      | ~ v2_pre_topc(X2)
% 7.73/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_38,negated_conjecture,
% 7.73/1.49      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_846,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X0,X2)
% 7.73/1.49      | ~ m1_pre_topc(X1,X2)
% 7.73/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 7.73/1.49      | ~ v1_funct_1(X3)
% 7.73/1.49      | v2_struct_0(X4)
% 7.73/1.49      | v2_struct_0(X2)
% 7.73/1.49      | ~ l1_pre_topc(X4)
% 7.73/1.49      | ~ l1_pre_topc(X2)
% 7.73/1.49      | ~ v2_pre_topc(X4)
% 7.73/1.49      | ~ v2_pre_topc(X2)
% 7.73/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 7.73/1.49      | u1_struct_0(X4) != u1_struct_0(sK1)
% 7.73/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 7.73/1.49      | sK4 != X3 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_847,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X1,X2)
% 7.73/1.49      | ~ m1_pre_topc(X0,X2)
% 7.73/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.73/1.49      | ~ v1_funct_1(sK4)
% 7.73/1.49      | v2_struct_0(X2)
% 7.73/1.49      | v2_struct_0(X3)
% 7.73/1.49      | ~ l1_pre_topc(X2)
% 7.73/1.49      | ~ l1_pre_topc(X3)
% 7.73/1.49      | ~ v2_pre_topc(X2)
% 7.73/1.49      | ~ v2_pre_topc(X3)
% 7.73/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.73/1.49      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.73/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_846]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_39,negated_conjecture,
% 7.73/1.49      ( v1_funct_1(sK4) ),
% 7.73/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_851,plain,
% 7.73/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.73/1.49      | ~ m1_pre_topc(X0,X2)
% 7.73/1.49      | ~ m1_pre_topc(X1,X2)
% 7.73/1.49      | ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | v2_struct_0(X2)
% 7.73/1.49      | v2_struct_0(X3)
% 7.73/1.49      | ~ l1_pre_topc(X2)
% 7.73/1.49      | ~ l1_pre_topc(X3)
% 7.73/1.49      | ~ v2_pre_topc(X2)
% 7.73/1.49      | ~ v2_pre_topc(X3)
% 7.73/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.73/1.49      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.73/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_847,c_39]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_852,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X1,X2)
% 7.73/1.49      | ~ m1_pre_topc(X0,X2)
% 7.73/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.73/1.49      | v2_struct_0(X2)
% 7.73/1.49      | v2_struct_0(X3)
% 7.73/1.49      | ~ l1_pre_topc(X2)
% 7.73/1.49      | ~ l1_pre_topc(X3)
% 7.73/1.49      | ~ v2_pre_topc(X2)
% 7.73/1.49      | ~ v2_pre_topc(X3)
% 7.73/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.73/1.49      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.73/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_851]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_883,plain,
% 7.73/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.49      | ~ m1_pre_topc(X1,X2)
% 7.73/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.73/1.49      | v2_struct_0(X2)
% 7.73/1.49      | v2_struct_0(X3)
% 7.73/1.49      | ~ l1_pre_topc(X2)
% 7.73/1.49      | ~ l1_pre_topc(X3)
% 7.73/1.49      | ~ v2_pre_topc(X2)
% 7.73/1.49      | ~ v2_pre_topc(X3)
% 7.73/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 7.73/1.49      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.73/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.49      inference(forward_subsumption_resolution,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_852,c_30]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9872,plain,
% 7.73/1.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 7.73/1.49      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.73/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.73/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 7.73/1.49      | m1_pre_topc(X0,X3) != iProver_top
% 7.73/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.73/1.49      | v2_struct_0(X3) = iProver_top
% 7.73/1.49      | v2_struct_0(X1) = iProver_top
% 7.73/1.49      | l1_pre_topc(X3) != iProver_top
% 7.73/1.49      | l1_pre_topc(X1) != iProver_top
% 7.73/1.49      | v2_pre_topc(X3) != iProver_top
% 7.73/1.49      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_883]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10561,plain,
% 7.73/1.49      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK3,X1,sK4)
% 7.73/1.49      | u1_struct_0(X0) != u1_struct_0(sK1)
% 7.73/1.49      | m1_pre_topc(X1,sK3) != iProver_top
% 7.73/1.49      | m1_pre_topc(sK3,X2) != iProver_top
% 7.73/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 7.73/1.49      | v2_struct_0(X0) = iProver_top
% 7.73/1.49      | v2_struct_0(X2) = iProver_top
% 7.73/1.49      | l1_pre_topc(X0) != iProver_top
% 7.73/1.49      | l1_pre_topc(X2) != iProver_top
% 7.73/1.49      | v2_pre_topc(X0) != iProver_top
% 7.73/1.49      | v2_pre_topc(X2) != iProver_top ),
% 7.73/1.49      inference(equality_resolution,[status(thm)],[c_9872]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10963,plain,
% 7.73/1.49      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | v2_struct_0(sK1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK1) != iProver_top ),
% 7.73/1.50      inference(equality_resolution,[status(thm)],[c_10561]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_46,negated_conjecture,
% 7.73/1.50      ( ~ v2_struct_0(sK1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_53,plain,
% 7.73/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_45,negated_conjecture,
% 7.73/1.50      ( v2_pre_topc(sK1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_54,plain,
% 7.73/1.50      ( v2_pre_topc(sK1) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_44,negated_conjecture,
% 7.73/1.50      ( l1_pre_topc(sK1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_55,plain,
% 7.73/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_37,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.73/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_62,plain,
% 7.73/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_136,plain,
% 7.73/1.50      ( r1_tarski(sK1,sK1) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_140,plain,
% 7.73/1.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1305,plain,
% 7.73/1.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.73/1.50      theory(equality) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1321,plain,
% 7.73/1.50      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1305]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10522,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,sK3)
% 7.73/1.50      | ~ m1_pre_topc(sK3,X1)
% 7.73/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(sK1)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(sK1)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(sK1)
% 7.73/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.73/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_883]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10523,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.73/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | v2_struct_0(sK1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_10522]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_1297,plain,( X0 = X0 ),theory(equality) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12985,plain,
% 7.73/1.50      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_1297]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14346,plain,
% 7.73/1.50      ( v2_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_10963,c_53,c_54,c_55,c_62,c_136,c_140,c_1321,c_10523,
% 7.73/1.50                 c_12985]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14347,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_14346]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9890,plain,
% 7.73/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10979,plain,
% 7.73/1.50      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_9890,c_9875]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14352,plain,
% 7.73/1.50      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK3,X0,sK4)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK3,X1) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_14347,c_10979,c_11362]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14364,plain,
% 7.73/1.50      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | v2_struct_0(sK0) = iProver_top
% 7.73/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_9894,c_14352]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_49,negated_conjecture,
% 7.73/1.50      ( ~ v2_struct_0(sK0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_50,plain,
% 7.73/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14709,plain,
% 7.73/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_14364,c_50,c_51,c_52]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_14710,plain,
% 7.73/1.50      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_14709]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19594,plain,
% 7.73/1.50      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_19585,c_14710]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_18,plain,
% 7.73/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.73/1.50      | ~ m1_pre_topc(X3,X1)
% 7.73/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ v1_funct_1(X0)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_897,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X3)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X3)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X3)
% 7.73/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 7.73/1.50      | u1_struct_0(X3) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK3)
% 7.73/1.50      | sK4 != X2 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_898,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ v1_funct_1(sK4)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 7.73/1.50      | u1_struct_0(X2) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_897]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_902,plain,
% 7.73/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 7.73/1.50      | u1_struct_0(X2) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_898,c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_903,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK4,X0)
% 7.73/1.50      | u1_struct_0(X2) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_902]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9871,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.73/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10417,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
% 7.73/1.50      | u1_struct_0(X0) != u1_struct_0(sK1)
% 7.73/1.50      | m1_pre_topc(X1,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | v2_struct_0(sK3) = iProver_top
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v2_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top ),
% 7.73/1.50      inference(equality_resolution,[status(thm)],[c_9871]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_41,negated_conjecture,
% 7.73/1.50      ( ~ v2_struct_0(sK3) ),
% 7.73/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_58,plain,
% 7.73/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10384,plain,
% 7.73/1.50      ( ~ m1_pre_topc(sK3,sK0)
% 7.73/1.50      | ~ l1_pre_topc(sK0)
% 7.73/1.50      | ~ v2_pre_topc(sK0)
% 7.73/1.50      | v2_pre_topc(sK3) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10391,plain,
% 7.73/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_10384]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10528,plain,
% 7.73/1.50      ( v2_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 7.73/1.50      | m1_pre_topc(X1,sK3) != iProver_top
% 7.73/1.50      | u1_struct_0(X0) != u1_struct_0(sK1)
% 7.73/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_10417,c_51,c_52,c_58,c_59,c_10387,c_10391]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10529,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0),sK4,u1_struct_0(X1)) = k2_tmap_1(sK3,X0,sK4,X1)
% 7.73/1.50      | u1_struct_0(X0) != u1_struct_0(sK1)
% 7.73/1.50      | m1_pre_topc(X1,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_pre_topc(X0) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_10528]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10541,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(sK1) = iProver_top
% 7.73/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK1) != iProver_top ),
% 7.73/1.50      inference(equality_resolution,[status(thm)],[c_10529]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10820,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_10541,c_53,c_54,c_55,c_62]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11039,plain,
% 7.73/1.50      ( k2_partfun1(u1_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_10979,c_10820]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_13188,plain,
% 7.73/1.50      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X0)) = k2_tmap_1(sK3,sK1,sK4,X0)
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_11039,c_11362]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19595,plain,
% 7.73/1.50      ( k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_19585,c_13188]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_19602,plain,
% 7.73/1.50      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_19594,c_19595]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_32,negated_conjecture,
% 7.73/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.73/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9898,plain,
% 7.73/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_33,negated_conjecture,
% 7.73/1.50      ( sK5 = sK6 ),
% 7.73/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9965,plain,
% 7.73/1.50      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_9898,c_33]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_20643,plain,
% 7.73/1.50      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,sK4,sK2),sK5) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_19602,c_9965]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_21,plain,
% 7.73/1.50      ( v1_tsep_1(X0,X1)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.73/1.50      | ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_23,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.73/1.50      | ~ l1_pre_topc(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_271,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.73/1.50      | v1_tsep_1(X0,X1)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X1) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_21,c_23]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_272,plain,
% 7.73/1.50      ( v1_tsep_1(X0,X1)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.73/1.50      | ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X1) ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_271]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_28,plain,
% 7.73/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.73/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.73/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.73/1.50      | ~ v1_tsep_1(X4,X0)
% 7.73/1.50      | ~ m1_pre_topc(X4,X0)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | v2_struct_0(X4)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X0) ),
% 7.73/1.50      inference(cnf_transformation,[],[f126]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_676,plain,
% 7.73/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.73/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.73/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X5),X6)
% 7.73/1.50      | ~ m1_pre_topc(X5,X6)
% 7.73/1.50      | ~ m1_pre_topc(X4,X0)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | v2_struct_0(X4)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | ~ l1_pre_topc(X6)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(X6)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | X4 != X5
% 7.73/1.50      | X0 != X6 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_272,c_28]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_677,plain,
% 7.73/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.73/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.73/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X4),X0)
% 7.73/1.50      | ~ m1_pre_topc(X4,X0)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X4)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X0) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_676]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9,plain,
% 7.73/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.73/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.73/1.50      | m1_subset_1(X2,u1_struct_0(X1))
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | ~ l1_pre_topc(X1) ),
% 7.73/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_713,plain,
% 7.73/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.73/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.73/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X4),X0)
% 7.73/1.50      | ~ m1_pre_topc(X4,X0)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X4)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(X1) ),
% 7.73/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_677,c_9]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_732,plain,
% 7.73/1.50      ( r1_tmap_1(X0,X1,X2,X3)
% 7.73/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X4),X0)
% 7.73/1.50      | ~ m1_pre_topc(X4,X0)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.73/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.73/1.50      | ~ v1_funct_1(X2)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X4)
% 7.73/1.50      | ~ l1_pre_topc(X0)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X0)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.73/1.50      | sK4 != X2 ),
% 7.73/1.50      inference(resolution_lifted,[status(thm)],[c_713,c_38]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_733,plain,
% 7.73/1.50      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 7.73/1.50      | r1_tmap_1(X2,X1,sK4,X3)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X2)
% 7.73/1.50      | ~ m1_pre_topc(X0,X2)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.73/1.50      | ~ v1_funct_1(sK4)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(unflattening,[status(thm)],[c_732]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_737,plain,
% 7.73/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.50      | ~ m1_pre_topc(X0,X2)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X2)
% 7.73/1.50      | r1_tmap_1(X2,X1,sK4,X3)
% 7.73/1.50      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_733,c_39]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_738,plain,
% 7.73/1.50      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 7.73/1.50      | r1_tmap_1(X2,X1,sK4,X3)
% 7.73/1.50      | ~ v3_pre_topc(u1_struct_0(X0),X2)
% 7.73/1.50      | ~ m1_pre_topc(X0,X2)
% 7.73/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.73/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.73/1.50      | v2_struct_0(X0)
% 7.73/1.50      | v2_struct_0(X1)
% 7.73/1.50      | v2_struct_0(X2)
% 7.73/1.50      | ~ l1_pre_topc(X1)
% 7.73/1.50      | ~ l1_pre_topc(X2)
% 7.73/1.50      | ~ v2_pre_topc(X1)
% 7.73/1.50      | ~ v2_pre_topc(X2)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_737]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9874,plain,
% 7.73/1.50      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 7.73/1.50      | u1_struct_0(X1) != u1_struct_0(sK3)
% 7.73/1.50      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK4,X2),X3) != iProver_top
% 7.73/1.50      | r1_tmap_1(X1,X0,sK4,X3) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X2),X1) != iProver_top
% 7.73/1.50      | m1_pre_topc(X2,X1) != iProver_top
% 7.73/1.50      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | v2_struct_0(X2) = iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top
% 7.73/1.50      | l1_pre_topc(X1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_pre_topc(X1) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10518,plain,
% 7.73/1.50      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 7.73/1.50      | r1_tmap_1(X1,sK1,k2_tmap_1(X0,sK1,sK4,X1),X2) != iProver_top
% 7.73/1.50      | r1_tmap_1(X0,sK1,sK4,X2) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 7.73/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | v2_struct_0(sK1) = iProver_top
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top
% 7.73/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.73/1.50      | v2_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK1) != iProver_top ),
% 7.73/1.50      inference(equality_resolution,[status(thm)],[c_9874]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10798,plain,
% 7.73/1.50      ( v2_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.73/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 7.73/1.50      | r1_tmap_1(X0,sK1,sK4,X2) = iProver_top
% 7.73/1.50      | r1_tmap_1(X1,sK1,k2_tmap_1(X0,sK1,sK4,X1),X2) != iProver_top
% 7.73/1.50      | u1_struct_0(X0) != u1_struct_0(sK3)
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_10518,c_53,c_54,c_55]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10799,plain,
% 7.73/1.50      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 7.73/1.50      | r1_tmap_1(X1,sK1,k2_tmap_1(X0,sK1,sK4,X1),X2) != iProver_top
% 7.73/1.50      | r1_tmap_1(X0,sK1,sK4,X2) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X1),X0) != iProver_top
% 7.73/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.73/1.50      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X1) = iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | l1_pre_topc(X0) != iProver_top
% 7.73/1.50      | v2_pre_topc(X0) != iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_10798]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10813,plain,
% 7.73/1.50      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
% 7.73/1.50      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.73/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top
% 7.73/1.50      | v2_struct_0(sK3) = iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top ),
% 7.73/1.50      inference(equality_resolution,[status(thm)],[c_10799]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10906,plain,
% 7.73/1.50      ( v2_struct_0(X0) = iProver_top
% 7.73/1.50      | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
% 7.73/1.50      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
% 7.73/1.50      inference(global_propositional_subsumption,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_10813,c_51,c_52,c_58,c_59,c_62,c_10387,c_10391]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_10907,plain,
% 7.73/1.50      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,sK4,X0),X1) != iProver_top
% 7.73/1.50      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(X0),sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(X0,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 7.73/1.50      | v2_struct_0(X0) = iProver_top ),
% 7.73/1.50      inference(renaming,[status(thm)],[c_10906]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_20685,plain,
% 7.73/1.50      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 7.73/1.50      | v3_pre_topc(u1_struct_0(sK2),sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 7.73/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.73/1.50      inference(superposition,[status(thm)],[c_20643,c_10907]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_17957,plain,
% 7.73/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_17926,c_11407]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_20686,plain,
% 7.73/1.50      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 7.73/1.50      | v3_pre_topc(k2_struct_0(sK3),sK3) != iProver_top
% 7.73/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.73/1.50      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 7.73/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.73/1.50      inference(light_normalisation,[status(thm)],[c_20685,c_17957]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12148,plain,
% 7.73/1.50      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.73/1.50      | ~ l1_pre_topc(sK3)
% 7.73/1.50      | ~ v2_pre_topc(sK3) ),
% 7.73/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_12155,plain,
% 7.73/1.50      ( v3_pre_topc(k2_struct_0(sK3),sK3) = iProver_top
% 7.73/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.73/1.50      | v2_pre_topc(sK3) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_12148]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_35,negated_conjecture,
% 7.73/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.73/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_9896,plain,
% 7.73/1.50      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_11489,plain,
% 7.73/1.50      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 7.73/1.50      inference(demodulation,[status(thm)],[c_11362,c_9896]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_31,negated_conjecture,
% 7.73/1.50      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.73/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_66,plain,
% 7.73/1.50      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_43,negated_conjecture,
% 7.73/1.50      ( ~ v2_struct_0(sK2) ),
% 7.73/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(c_56,plain,
% 7.73/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.73/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.73/1.50  
% 7.73/1.50  cnf(contradiction,plain,
% 7.73/1.50      ( $false ),
% 7.73/1.50      inference(minisat,
% 7.73/1.50                [status(thm)],
% 7.73/1.50                [c_20686,c_19535,c_12155,c_11489,c_10430,c_10391,c_10387,
% 7.73/1.50                 c_66,c_59,c_57,c_56,c_52,c_51]) ).
% 7.73/1.50  
% 7.73/1.50  
% 7.73/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.50  
% 7.73/1.50  ------                               Statistics
% 7.73/1.50  
% 7.73/1.50  ------ Selected
% 7.73/1.50  
% 7.73/1.50  total_time:                             0.541
% 7.73/1.50  
%------------------------------------------------------------------------------
