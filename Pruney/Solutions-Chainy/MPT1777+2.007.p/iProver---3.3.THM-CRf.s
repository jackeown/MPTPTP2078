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

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4471)

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7)
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
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
            ( ~ r1_tmap_1(X3,X1,X4,sK6)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
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
                ( ~ r1_tmap_1(X3,X1,sK5,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
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
                    ( ~ r1_tmap_1(sK4,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
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
                        & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
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
                            ( ~ r1_tmap_1(X3,sK2,X4,X5)
                            & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f51,f50,f49,f48,f47,f46,f45])).

fof(f79,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
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

fof(f93,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f83,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1911,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1921,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1919,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2058,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1921,c_1919])).

cnf(c_4865,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_2058])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5657,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4865,c_39,c_40,c_3424,c_4471,c_5540])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1913,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4864,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_2058])).

cnf(c_5637,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4864,c_39,c_40,c_47,c_3423,c_3794,c_5517])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1931,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5645,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK4)
    | m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5637,c_1931])).

cnf(c_6069,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3)
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5657,c_5645])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1925,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3423,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_1925])).

cnf(c_3424,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1925])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4939,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4944,plain,
    ( m1_pre_topc(sK3,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4939])).

cnf(c_3436,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3423,c_40])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1927,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3752,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
    | v1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3436,c_1927])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1924,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3668,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1924])).

cnf(c_4994,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3752,c_40,c_44,c_3424,c_3668])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_198,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_7])).

cnf(c_199,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_1903,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(X2,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_3546,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK4
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1903])).

cnf(c_4019,plain,
    ( l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK4
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3546,c_40,c_3424])).

cnf(c_4020,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK4
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4019])).

cnf(c_4029,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4020])).

cnf(c_4162,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK3,X1) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_40,c_3424])).

cnf(c_4163,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4162])).

cnf(c_4173,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
    | m1_pre_topc(sK3,X0) = iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4163])).

cnf(c_5001,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top
    | m1_pre_topc(sK3,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4994,c_4173])).

cnf(c_4030,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_4020])).

cnf(c_5000,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
    | m1_pre_topc(sK3,sK3) != iProver_top
    | m1_pre_topc(sK4,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4994,c_4030])).

cnf(c_5810,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK4,X0) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5000,c_40,c_3423,c_3424,c_4944])).

cnf(c_5811,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
    | m1_pre_topc(sK4,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5810])).

cnf(c_5819,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_5811])).

cnf(c_6429,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6069,c_40,c_3423,c_3424,c_4944,c_5001,c_5819])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1917,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1971,plain,
    ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1917,c_21])).

cnf(c_12,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_554,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_555,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_559,plain,
    ( ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X5,X3,X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_27])).

cnf(c_560,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_607,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_connsp_2(X5,X3,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_560,c_16])).

cnf(c_652,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(X7,u1_struct_0(X0))
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X3 != X6
    | X4 != X5
    | sK0(X6,X5) != X7
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_607])).

cnf(c_653,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_678,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_653,c_632])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_699,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | u1_struct_0(X3) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_678,c_7,c_6])).

cnf(c_1901,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(sK0(X1,X4),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_2838,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1901])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2965,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2838,c_41,c_42,c_43])).

cnf(c_2966,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
    | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2965])).

cnf(c_2983,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2966])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3311,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2983,c_46,c_50])).

cnf(c_3312,plain,
    ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3311])).

cnf(c_3328,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_3312])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_54,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1916,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1958,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1916,c_21])).

cnf(c_3352,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3328,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1958])).

cnf(c_6434,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6429,c_3352])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4195,plain,
    ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_4196,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4195])).

cnf(c_2703,plain,
    ( ~ m1_pre_topc(sK4,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3793,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2703])).

cnf(c_3794,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3793])).

cnf(c_2265,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_2266,plain,
    ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2265])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6434,c_5001,c_4944,c_4196,c_3794,c_3424,c_3423,c_2266,c_51,c_47,c_46,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.00  
% 2.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.96/1.00  
% 2.96/1.00  ------  iProver source info
% 2.96/1.00  
% 2.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.96/1.00  git: non_committed_changes: false
% 2.96/1.00  git: last_make_outside_of_git: false
% 2.96/1.00  
% 2.96/1.00  ------ 
% 2.96/1.00  
% 2.96/1.00  ------ Input Options
% 2.96/1.00  
% 2.96/1.00  --out_options                           all
% 2.96/1.00  --tptp_safe_out                         true
% 2.96/1.00  --problem_path                          ""
% 2.96/1.00  --include_path                          ""
% 2.96/1.00  --clausifier                            res/vclausify_rel
% 2.96/1.00  --clausifier_options                    --mode clausify
% 2.96/1.00  --stdin                                 false
% 2.96/1.00  --stats_out                             all
% 2.96/1.00  
% 2.96/1.00  ------ General Options
% 2.96/1.00  
% 2.96/1.00  --fof                                   false
% 2.96/1.00  --time_out_real                         305.
% 2.96/1.00  --time_out_virtual                      -1.
% 2.96/1.00  --symbol_type_check                     false
% 2.96/1.00  --clausify_out                          false
% 2.96/1.00  --sig_cnt_out                           false
% 2.96/1.00  --trig_cnt_out                          false
% 2.96/1.00  --trig_cnt_out_tolerance                1.
% 2.96/1.00  --trig_cnt_out_sk_spl                   false
% 2.96/1.00  --abstr_cl_out                          false
% 2.96/1.00  
% 2.96/1.00  ------ Global Options
% 2.96/1.00  
% 2.96/1.00  --schedule                              default
% 2.96/1.00  --add_important_lit                     false
% 2.96/1.00  --prop_solver_per_cl                    1000
% 2.96/1.00  --min_unsat_core                        false
% 2.96/1.00  --soft_assumptions                      false
% 2.96/1.00  --soft_lemma_size                       3
% 2.96/1.00  --prop_impl_unit_size                   0
% 2.96/1.00  --prop_impl_unit                        []
% 2.96/1.00  --share_sel_clauses                     true
% 2.96/1.00  --reset_solvers                         false
% 2.96/1.00  --bc_imp_inh                            [conj_cone]
% 2.96/1.00  --conj_cone_tolerance                   3.
% 2.96/1.00  --extra_neg_conj                        none
% 2.96/1.00  --large_theory_mode                     true
% 2.96/1.00  --prolific_symb_bound                   200
% 2.96/1.00  --lt_threshold                          2000
% 2.96/1.00  --clause_weak_htbl                      true
% 2.96/1.00  --gc_record_bc_elim                     false
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing Options
% 2.96/1.00  
% 2.96/1.00  --preprocessing_flag                    true
% 2.96/1.00  --time_out_prep_mult                    0.1
% 2.96/1.00  --splitting_mode                        input
% 2.96/1.00  --splitting_grd                         true
% 2.96/1.00  --splitting_cvd                         false
% 2.96/1.00  --splitting_cvd_svl                     false
% 2.96/1.00  --splitting_nvd                         32
% 2.96/1.00  --sub_typing                            true
% 2.96/1.00  --prep_gs_sim                           true
% 2.96/1.00  --prep_unflatten                        true
% 2.96/1.00  --prep_res_sim                          true
% 2.96/1.00  --prep_upred                            true
% 2.96/1.00  --prep_sem_filter                       exhaustive
% 2.96/1.00  --prep_sem_filter_out                   false
% 2.96/1.00  --pred_elim                             true
% 2.96/1.00  --res_sim_input                         true
% 2.96/1.00  --eq_ax_congr_red                       true
% 2.96/1.00  --pure_diseq_elim                       true
% 2.96/1.00  --brand_transform                       false
% 2.96/1.00  --non_eq_to_eq                          false
% 2.96/1.00  --prep_def_merge                        true
% 2.96/1.00  --prep_def_merge_prop_impl              false
% 2.96/1.00  --prep_def_merge_mbd                    true
% 2.96/1.00  --prep_def_merge_tr_red                 false
% 2.96/1.00  --prep_def_merge_tr_cl                  false
% 2.96/1.00  --smt_preprocessing                     true
% 2.96/1.00  --smt_ac_axioms                         fast
% 2.96/1.00  --preprocessed_out                      false
% 2.96/1.00  --preprocessed_stats                    false
% 2.96/1.00  
% 2.96/1.00  ------ Abstraction refinement Options
% 2.96/1.00  
% 2.96/1.00  --abstr_ref                             []
% 2.96/1.00  --abstr_ref_prep                        false
% 2.96/1.00  --abstr_ref_until_sat                   false
% 2.96/1.00  --abstr_ref_sig_restrict                funpre
% 2.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/1.00  --abstr_ref_under                       []
% 2.96/1.00  
% 2.96/1.00  ------ SAT Options
% 2.96/1.00  
% 2.96/1.00  --sat_mode                              false
% 2.96/1.00  --sat_fm_restart_options                ""
% 2.96/1.00  --sat_gr_def                            false
% 2.96/1.00  --sat_epr_types                         true
% 2.96/1.00  --sat_non_cyclic_types                  false
% 2.96/1.00  --sat_finite_models                     false
% 2.96/1.00  --sat_fm_lemmas                         false
% 2.96/1.00  --sat_fm_prep                           false
% 2.96/1.00  --sat_fm_uc_incr                        true
% 2.96/1.00  --sat_out_model                         small
% 2.96/1.00  --sat_out_clauses                       false
% 2.96/1.00  
% 2.96/1.00  ------ QBF Options
% 2.96/1.00  
% 2.96/1.00  --qbf_mode                              false
% 2.96/1.00  --qbf_elim_univ                         false
% 2.96/1.00  --qbf_dom_inst                          none
% 2.96/1.00  --qbf_dom_pre_inst                      false
% 2.96/1.00  --qbf_sk_in                             false
% 2.96/1.00  --qbf_pred_elim                         true
% 2.96/1.00  --qbf_split                             512
% 2.96/1.00  
% 2.96/1.00  ------ BMC1 Options
% 2.96/1.00  
% 2.96/1.00  --bmc1_incremental                      false
% 2.96/1.00  --bmc1_axioms                           reachable_all
% 2.96/1.00  --bmc1_min_bound                        0
% 2.96/1.00  --bmc1_max_bound                        -1
% 2.96/1.00  --bmc1_max_bound_default                -1
% 2.96/1.00  --bmc1_symbol_reachability              true
% 2.96/1.00  --bmc1_property_lemmas                  false
% 2.96/1.00  --bmc1_k_induction                      false
% 2.96/1.00  --bmc1_non_equiv_states                 false
% 2.96/1.00  --bmc1_deadlock                         false
% 2.96/1.00  --bmc1_ucm                              false
% 2.96/1.00  --bmc1_add_unsat_core                   none
% 2.96/1.00  --bmc1_unsat_core_children              false
% 2.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/1.00  --bmc1_out_stat                         full
% 2.96/1.00  --bmc1_ground_init                      false
% 2.96/1.00  --bmc1_pre_inst_next_state              false
% 2.96/1.00  --bmc1_pre_inst_state                   false
% 2.96/1.00  --bmc1_pre_inst_reach_state             false
% 2.96/1.00  --bmc1_out_unsat_core                   false
% 2.96/1.00  --bmc1_aig_witness_out                  false
% 2.96/1.00  --bmc1_verbose                          false
% 2.96/1.00  --bmc1_dump_clauses_tptp                false
% 2.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.96/1.00  --bmc1_dump_file                        -
% 2.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.96/1.00  --bmc1_ucm_extend_mode                  1
% 2.96/1.00  --bmc1_ucm_init_mode                    2
% 2.96/1.00  --bmc1_ucm_cone_mode                    none
% 2.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.96/1.00  --bmc1_ucm_relax_model                  4
% 2.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/1.00  --bmc1_ucm_layered_model                none
% 2.96/1.00  --bmc1_ucm_max_lemma_size               10
% 2.96/1.00  
% 2.96/1.00  ------ AIG Options
% 2.96/1.00  
% 2.96/1.00  --aig_mode                              false
% 2.96/1.00  
% 2.96/1.00  ------ Instantiation Options
% 2.96/1.00  
% 2.96/1.00  --instantiation_flag                    true
% 2.96/1.00  --inst_sos_flag                         false
% 2.96/1.00  --inst_sos_phase                        true
% 2.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/1.00  --inst_lit_sel_side                     num_symb
% 2.96/1.00  --inst_solver_per_active                1400
% 2.96/1.00  --inst_solver_calls_frac                1.
% 2.96/1.00  --inst_passive_queue_type               priority_queues
% 2.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/1.00  --inst_passive_queues_freq              [25;2]
% 2.96/1.00  --inst_dismatching                      true
% 2.96/1.00  --inst_eager_unprocessed_to_passive     true
% 2.96/1.00  --inst_prop_sim_given                   true
% 2.96/1.00  --inst_prop_sim_new                     false
% 2.96/1.00  --inst_subs_new                         false
% 2.96/1.00  --inst_eq_res_simp                      false
% 2.96/1.00  --inst_subs_given                       false
% 2.96/1.00  --inst_orphan_elimination               true
% 2.96/1.00  --inst_learning_loop_flag               true
% 2.96/1.00  --inst_learning_start                   3000
% 2.96/1.00  --inst_learning_factor                  2
% 2.96/1.00  --inst_start_prop_sim_after_learn       3
% 2.96/1.00  --inst_sel_renew                        solver
% 2.96/1.00  --inst_lit_activity_flag                true
% 2.96/1.00  --inst_restr_to_given                   false
% 2.96/1.00  --inst_activity_threshold               500
% 2.96/1.00  --inst_out_proof                        true
% 2.96/1.00  
% 2.96/1.00  ------ Resolution Options
% 2.96/1.00  
% 2.96/1.00  --resolution_flag                       true
% 2.96/1.00  --res_lit_sel                           adaptive
% 2.96/1.00  --res_lit_sel_side                      none
% 2.96/1.00  --res_ordering                          kbo
% 2.96/1.00  --res_to_prop_solver                    active
% 2.96/1.00  --res_prop_simpl_new                    false
% 2.96/1.00  --res_prop_simpl_given                  true
% 2.96/1.00  --res_passive_queue_type                priority_queues
% 2.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/1.00  --res_passive_queues_freq               [15;5]
% 2.96/1.00  --res_forward_subs                      full
% 2.96/1.00  --res_backward_subs                     full
% 2.96/1.00  --res_forward_subs_resolution           true
% 2.96/1.00  --res_backward_subs_resolution          true
% 2.96/1.00  --res_orphan_elimination                true
% 2.96/1.00  --res_time_limit                        2.
% 2.96/1.00  --res_out_proof                         true
% 2.96/1.00  
% 2.96/1.00  ------ Superposition Options
% 2.96/1.00  
% 2.96/1.00  --superposition_flag                    true
% 2.96/1.00  --sup_passive_queue_type                priority_queues
% 2.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.96/1.00  --demod_completeness_check              fast
% 2.96/1.00  --demod_use_ground                      true
% 2.96/1.00  --sup_to_prop_solver                    passive
% 2.96/1.00  --sup_prop_simpl_new                    true
% 2.96/1.00  --sup_prop_simpl_given                  true
% 2.96/1.00  --sup_fun_splitting                     false
% 2.96/1.00  --sup_smt_interval                      50000
% 2.96/1.00  
% 2.96/1.00  ------ Superposition Simplification Setup
% 2.96/1.00  
% 2.96/1.00  --sup_indices_passive                   []
% 2.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.00  --sup_full_bw                           [BwDemod]
% 2.96/1.00  --sup_immed_triv                        [TrivRules]
% 2.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.00  --sup_immed_bw_main                     []
% 2.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.00  
% 2.96/1.00  ------ Combination Options
% 2.96/1.00  
% 2.96/1.00  --comb_res_mult                         3
% 2.96/1.00  --comb_sup_mult                         2
% 2.96/1.00  --comb_inst_mult                        10
% 2.96/1.00  
% 2.96/1.00  ------ Debug Options
% 2.96/1.00  
% 2.96/1.00  --dbg_backtrace                         false
% 2.96/1.00  --dbg_dump_prop_clauses                 false
% 2.96/1.00  --dbg_dump_prop_clauses_file            -
% 2.96/1.00  --dbg_out_stat                          false
% 2.96/1.00  ------ Parsing...
% 2.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.96/1.00  ------ Proving...
% 2.96/1.00  ------ Problem Properties 
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  clauses                                 34
% 2.96/1.00  conjectures                             17
% 2.96/1.00  EPR                                     18
% 2.96/1.00  Horn                                    30
% 2.96/1.00  unary                                   18
% 2.96/1.00  binary                                  3
% 2.96/1.00  lits                                    108
% 2.96/1.00  lits eq                                 10
% 2.96/1.00  fd_pure                                 0
% 2.96/1.00  fd_pseudo                               0
% 2.96/1.00  fd_cond                                 0
% 2.96/1.00  fd_pseudo_cond                          1
% 2.96/1.00  AC symbols                              0
% 2.96/1.00  
% 2.96/1.00  ------ Schedule dynamic 5 is on 
% 2.96/1.00  
% 2.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  ------ 
% 2.96/1.00  Current options:
% 2.96/1.00  ------ 
% 2.96/1.00  
% 2.96/1.00  ------ Input Options
% 2.96/1.00  
% 2.96/1.00  --out_options                           all
% 2.96/1.00  --tptp_safe_out                         true
% 2.96/1.00  --problem_path                          ""
% 2.96/1.00  --include_path                          ""
% 2.96/1.00  --clausifier                            res/vclausify_rel
% 2.96/1.00  --clausifier_options                    --mode clausify
% 2.96/1.00  --stdin                                 false
% 2.96/1.00  --stats_out                             all
% 2.96/1.00  
% 2.96/1.00  ------ General Options
% 2.96/1.00  
% 2.96/1.00  --fof                                   false
% 2.96/1.00  --time_out_real                         305.
% 2.96/1.00  --time_out_virtual                      -1.
% 2.96/1.00  --symbol_type_check                     false
% 2.96/1.00  --clausify_out                          false
% 2.96/1.00  --sig_cnt_out                           false
% 2.96/1.00  --trig_cnt_out                          false
% 2.96/1.00  --trig_cnt_out_tolerance                1.
% 2.96/1.00  --trig_cnt_out_sk_spl                   false
% 2.96/1.00  --abstr_cl_out                          false
% 2.96/1.00  
% 2.96/1.00  ------ Global Options
% 2.96/1.00  
% 2.96/1.00  --schedule                              default
% 2.96/1.00  --add_important_lit                     false
% 2.96/1.00  --prop_solver_per_cl                    1000
% 2.96/1.00  --min_unsat_core                        false
% 2.96/1.00  --soft_assumptions                      false
% 2.96/1.00  --soft_lemma_size                       3
% 2.96/1.00  --prop_impl_unit_size                   0
% 2.96/1.00  --prop_impl_unit                        []
% 2.96/1.00  --share_sel_clauses                     true
% 2.96/1.00  --reset_solvers                         false
% 2.96/1.00  --bc_imp_inh                            [conj_cone]
% 2.96/1.00  --conj_cone_tolerance                   3.
% 2.96/1.00  --extra_neg_conj                        none
% 2.96/1.00  --large_theory_mode                     true
% 2.96/1.00  --prolific_symb_bound                   200
% 2.96/1.00  --lt_threshold                          2000
% 2.96/1.00  --clause_weak_htbl                      true
% 2.96/1.00  --gc_record_bc_elim                     false
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing Options
% 2.96/1.00  
% 2.96/1.00  --preprocessing_flag                    true
% 2.96/1.00  --time_out_prep_mult                    0.1
% 2.96/1.00  --splitting_mode                        input
% 2.96/1.00  --splitting_grd                         true
% 2.96/1.00  --splitting_cvd                         false
% 2.96/1.00  --splitting_cvd_svl                     false
% 2.96/1.00  --splitting_nvd                         32
% 2.96/1.00  --sub_typing                            true
% 2.96/1.00  --prep_gs_sim                           true
% 2.96/1.00  --prep_unflatten                        true
% 2.96/1.00  --prep_res_sim                          true
% 2.96/1.00  --prep_upred                            true
% 2.96/1.00  --prep_sem_filter                       exhaustive
% 2.96/1.00  --prep_sem_filter_out                   false
% 2.96/1.00  --pred_elim                             true
% 2.96/1.00  --res_sim_input                         true
% 2.96/1.00  --eq_ax_congr_red                       true
% 2.96/1.00  --pure_diseq_elim                       true
% 2.96/1.00  --brand_transform                       false
% 2.96/1.00  --non_eq_to_eq                          false
% 2.96/1.00  --prep_def_merge                        true
% 2.96/1.00  --prep_def_merge_prop_impl              false
% 2.96/1.00  --prep_def_merge_mbd                    true
% 2.96/1.00  --prep_def_merge_tr_red                 false
% 2.96/1.00  --prep_def_merge_tr_cl                  false
% 2.96/1.00  --smt_preprocessing                     true
% 2.96/1.00  --smt_ac_axioms                         fast
% 2.96/1.00  --preprocessed_out                      false
% 2.96/1.00  --preprocessed_stats                    false
% 2.96/1.00  
% 2.96/1.00  ------ Abstraction refinement Options
% 2.96/1.00  
% 2.96/1.00  --abstr_ref                             []
% 2.96/1.00  --abstr_ref_prep                        false
% 2.96/1.00  --abstr_ref_until_sat                   false
% 2.96/1.00  --abstr_ref_sig_restrict                funpre
% 2.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/1.00  --abstr_ref_under                       []
% 2.96/1.00  
% 2.96/1.00  ------ SAT Options
% 2.96/1.00  
% 2.96/1.00  --sat_mode                              false
% 2.96/1.00  --sat_fm_restart_options                ""
% 2.96/1.00  --sat_gr_def                            false
% 2.96/1.00  --sat_epr_types                         true
% 2.96/1.00  --sat_non_cyclic_types                  false
% 2.96/1.00  --sat_finite_models                     false
% 2.96/1.00  --sat_fm_lemmas                         false
% 2.96/1.00  --sat_fm_prep                           false
% 2.96/1.00  --sat_fm_uc_incr                        true
% 2.96/1.00  --sat_out_model                         small
% 2.96/1.00  --sat_out_clauses                       false
% 2.96/1.00  
% 2.96/1.00  ------ QBF Options
% 2.96/1.00  
% 2.96/1.00  --qbf_mode                              false
% 2.96/1.00  --qbf_elim_univ                         false
% 2.96/1.00  --qbf_dom_inst                          none
% 2.96/1.00  --qbf_dom_pre_inst                      false
% 2.96/1.00  --qbf_sk_in                             false
% 2.96/1.00  --qbf_pred_elim                         true
% 2.96/1.00  --qbf_split                             512
% 2.96/1.00  
% 2.96/1.00  ------ BMC1 Options
% 2.96/1.00  
% 2.96/1.00  --bmc1_incremental                      false
% 2.96/1.00  --bmc1_axioms                           reachable_all
% 2.96/1.00  --bmc1_min_bound                        0
% 2.96/1.00  --bmc1_max_bound                        -1
% 2.96/1.00  --bmc1_max_bound_default                -1
% 2.96/1.00  --bmc1_symbol_reachability              true
% 2.96/1.00  --bmc1_property_lemmas                  false
% 2.96/1.00  --bmc1_k_induction                      false
% 2.96/1.00  --bmc1_non_equiv_states                 false
% 2.96/1.00  --bmc1_deadlock                         false
% 2.96/1.00  --bmc1_ucm                              false
% 2.96/1.00  --bmc1_add_unsat_core                   none
% 2.96/1.00  --bmc1_unsat_core_children              false
% 2.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/1.00  --bmc1_out_stat                         full
% 2.96/1.00  --bmc1_ground_init                      false
% 2.96/1.00  --bmc1_pre_inst_next_state              false
% 2.96/1.00  --bmc1_pre_inst_state                   false
% 2.96/1.00  --bmc1_pre_inst_reach_state             false
% 2.96/1.00  --bmc1_out_unsat_core                   false
% 2.96/1.00  --bmc1_aig_witness_out                  false
% 2.96/1.00  --bmc1_verbose                          false
% 2.96/1.00  --bmc1_dump_clauses_tptp                false
% 2.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.96/1.00  --bmc1_dump_file                        -
% 2.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.96/1.00  --bmc1_ucm_extend_mode                  1
% 2.96/1.00  --bmc1_ucm_init_mode                    2
% 2.96/1.00  --bmc1_ucm_cone_mode                    none
% 2.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.96/1.00  --bmc1_ucm_relax_model                  4
% 2.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/1.00  --bmc1_ucm_layered_model                none
% 2.96/1.00  --bmc1_ucm_max_lemma_size               10
% 2.96/1.00  
% 2.96/1.00  ------ AIG Options
% 2.96/1.00  
% 2.96/1.00  --aig_mode                              false
% 2.96/1.00  
% 2.96/1.00  ------ Instantiation Options
% 2.96/1.00  
% 2.96/1.00  --instantiation_flag                    true
% 2.96/1.00  --inst_sos_flag                         false
% 2.96/1.00  --inst_sos_phase                        true
% 2.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/1.00  --inst_lit_sel_side                     none
% 2.96/1.00  --inst_solver_per_active                1400
% 2.96/1.00  --inst_solver_calls_frac                1.
% 2.96/1.00  --inst_passive_queue_type               priority_queues
% 2.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/1.00  --inst_passive_queues_freq              [25;2]
% 2.96/1.00  --inst_dismatching                      true
% 2.96/1.00  --inst_eager_unprocessed_to_passive     true
% 2.96/1.00  --inst_prop_sim_given                   true
% 2.96/1.00  --inst_prop_sim_new                     false
% 2.96/1.00  --inst_subs_new                         false
% 2.96/1.00  --inst_eq_res_simp                      false
% 2.96/1.00  --inst_subs_given                       false
% 2.96/1.00  --inst_orphan_elimination               true
% 2.96/1.00  --inst_learning_loop_flag               true
% 2.96/1.00  --inst_learning_start                   3000
% 2.96/1.00  --inst_learning_factor                  2
% 2.96/1.00  --inst_start_prop_sim_after_learn       3
% 2.96/1.00  --inst_sel_renew                        solver
% 2.96/1.00  --inst_lit_activity_flag                true
% 2.96/1.00  --inst_restr_to_given                   false
% 2.96/1.00  --inst_activity_threshold               500
% 2.96/1.00  --inst_out_proof                        true
% 2.96/1.00  
% 2.96/1.00  ------ Resolution Options
% 2.96/1.00  
% 2.96/1.00  --resolution_flag                       false
% 2.96/1.00  --res_lit_sel                           adaptive
% 2.96/1.00  --res_lit_sel_side                      none
% 2.96/1.00  --res_ordering                          kbo
% 2.96/1.00  --res_to_prop_solver                    active
% 2.96/1.00  --res_prop_simpl_new                    false
% 2.96/1.00  --res_prop_simpl_given                  true
% 2.96/1.00  --res_passive_queue_type                priority_queues
% 2.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/1.00  --res_passive_queues_freq               [15;5]
% 2.96/1.00  --res_forward_subs                      full
% 2.96/1.00  --res_backward_subs                     full
% 2.96/1.00  --res_forward_subs_resolution           true
% 2.96/1.00  --res_backward_subs_resolution          true
% 2.96/1.00  --res_orphan_elimination                true
% 2.96/1.00  --res_time_limit                        2.
% 2.96/1.00  --res_out_proof                         true
% 2.96/1.00  
% 2.96/1.00  ------ Superposition Options
% 2.96/1.00  
% 2.96/1.00  --superposition_flag                    true
% 2.96/1.00  --sup_passive_queue_type                priority_queues
% 2.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.96/1.00  --demod_completeness_check              fast
% 2.96/1.00  --demod_use_ground                      true
% 2.96/1.00  --sup_to_prop_solver                    passive
% 2.96/1.00  --sup_prop_simpl_new                    true
% 2.96/1.00  --sup_prop_simpl_given                  true
% 2.96/1.00  --sup_fun_splitting                     false
% 2.96/1.00  --sup_smt_interval                      50000
% 2.96/1.00  
% 2.96/1.00  ------ Superposition Simplification Setup
% 2.96/1.00  
% 2.96/1.00  --sup_indices_passive                   []
% 2.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.00  --sup_full_bw                           [BwDemod]
% 2.96/1.00  --sup_immed_triv                        [TrivRules]
% 2.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.00  --sup_immed_bw_main                     []
% 2.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/1.00  
% 2.96/1.00  ------ Combination Options
% 2.96/1.00  
% 2.96/1.00  --comb_res_mult                         3
% 2.96/1.00  --comb_sup_mult                         2
% 2.96/1.00  --comb_inst_mult                        10
% 2.96/1.00  
% 2.96/1.00  ------ Debug Options
% 2.96/1.00  
% 2.96/1.00  --dbg_backtrace                         false
% 2.96/1.00  --dbg_dump_prop_clauses                 false
% 2.96/1.00  --dbg_dump_prop_clauses_file            -
% 2.96/1.00  --dbg_out_stat                          false
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  ------ Proving...
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  % SZS status Theorem for theBenchmark.p
% 2.96/1.00  
% 2.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.96/1.00  
% 2.96/1.00  fof(f14,conjecture,(
% 2.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f15,negated_conjecture,(
% 2.96/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.96/1.00    inference(negated_conjecture,[],[f14])).
% 2.96/1.00  
% 2.96/1.00  fof(f36,plain,(
% 2.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f15])).
% 2.96/1.00  
% 2.96/1.00  fof(f37,plain,(
% 2.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.96/1.00    inference(flattening,[],[f36])).
% 2.96/1.00  
% 2.96/1.00  fof(f51,plain,(
% 2.96/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK7) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f50,plain,(
% 2.96/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK6) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f49,plain,(
% 2.96/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK5,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f48,plain,(
% 2.96/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK4,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f47,plain,(
% 2.96/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK3,X1,k3_tmap_1(X0,X1,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f46,plain,(
% 2.96/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(X0,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f45,plain,(
% 2.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f52,plain,(
% 2.96/1.00    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f37,f51,f50,f49,f48,f47,f46,f45])).
% 2.96/1.00  
% 2.96/1.00  fof(f79,plain,(
% 2.96/1.00    m1_pre_topc(sK3,sK1)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f11,axiom,(
% 2.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f30,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f11])).
% 2.96/1.00  
% 2.96/1.00  fof(f31,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/1.00    inference(flattening,[],[f30])).
% 2.96/1.00  
% 2.96/1.00  fof(f43,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/1.00    inference(nnf_transformation,[],[f31])).
% 2.96/1.00  
% 2.96/1.00  fof(f68,plain,(
% 2.96/1.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f43])).
% 2.96/1.00  
% 2.96/1.00  fof(f12,axiom,(
% 2.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f32,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f12])).
% 2.96/1.00  
% 2.96/1.00  fof(f33,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/1.00    inference(flattening,[],[f32])).
% 2.96/1.00  
% 2.96/1.00  fof(f69,plain,(
% 2.96/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f33])).
% 2.96/1.00  
% 2.96/1.00  fof(f73,plain,(
% 2.96/1.00    v2_pre_topc(sK1)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f74,plain,(
% 2.96/1.00    l1_pre_topc(sK1)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f81,plain,(
% 2.96/1.00    m1_pre_topc(sK4,sK1)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f1,axiom,(
% 2.96/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f38,plain,(
% 2.96/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/1.00    inference(nnf_transformation,[],[f1])).
% 2.96/1.00  
% 2.96/1.00  fof(f39,plain,(
% 2.96/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.96/1.00    inference(flattening,[],[f38])).
% 2.96/1.00  
% 2.96/1.00  fof(f55,plain,(
% 2.96/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f39])).
% 2.96/1.00  
% 2.96/1.00  fof(f5,axiom,(
% 2.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f20,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.96/1.00    inference(ennf_transformation,[],[f5])).
% 2.96/1.00  
% 2.96/1.00  fof(f60,plain,(
% 2.96/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f20])).
% 2.96/1.00  
% 2.96/1.00  fof(f10,axiom,(
% 2.96/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f29,plain,(
% 2.96/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.96/1.00    inference(ennf_transformation,[],[f10])).
% 2.96/1.00  
% 2.96/1.00  fof(f66,plain,(
% 2.96/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f29])).
% 2.96/1.00  
% 2.96/1.00  fof(f3,axiom,(
% 2.96/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f16,plain,(
% 2.96/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.96/1.00    inference(ennf_transformation,[],[f3])).
% 2.96/1.00  
% 2.96/1.00  fof(f17,plain,(
% 2.96/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.96/1.00    inference(flattening,[],[f16])).
% 2.96/1.00  
% 2.96/1.00  fof(f58,plain,(
% 2.96/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f17])).
% 2.96/1.00  
% 2.96/1.00  fof(f78,plain,(
% 2.96/1.00    ~v2_struct_0(sK3)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f85,plain,(
% 2.96/1.00    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f6,axiom,(
% 2.96/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f21,plain,(
% 2.96/1.00    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f6])).
% 2.96/1.00  
% 2.96/1.00  fof(f22,plain,(
% 2.96/1.00    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/1.00    inference(flattening,[],[f21])).
% 2.96/1.00  
% 2.96/1.00  fof(f62,plain,(
% 2.96/1.00    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f22])).
% 2.96/1.00  
% 2.96/1.00  fof(f7,axiom,(
% 2.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f23,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.96/1.00    inference(ennf_transformation,[],[f7])).
% 2.96/1.00  
% 2.96/1.00  fof(f24,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.96/1.00    inference(flattening,[],[f23])).
% 2.96/1.00  
% 2.96/1.00  fof(f63,plain,(
% 2.96/1.00    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f24])).
% 2.96/1.00  
% 2.96/1.00  fof(f89,plain,(
% 2.96/1.00    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f88,plain,(
% 2.96/1.00    sK6 = sK7),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f9,axiom,(
% 2.96/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f27,plain,(
% 2.96/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f9])).
% 2.96/1.00  
% 2.96/1.00  fof(f28,plain,(
% 2.96/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/1.00    inference(flattening,[],[f27])).
% 2.96/1.00  
% 2.96/1.00  fof(f41,plain,(
% 2.96/1.00    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.96/1.00    introduced(choice_axiom,[])).
% 2.96/1.00  
% 2.96/1.00  fof(f42,plain,(
% 2.96/1.00    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f41])).
% 2.96/1.00  
% 2.96/1.00  fof(f65,plain,(
% 2.96/1.00    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f42])).
% 2.96/1.00  
% 2.96/1.00  fof(f13,axiom,(
% 2.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f34,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f13])).
% 2.96/1.00  
% 2.96/1.00  fof(f35,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/1.00    inference(flattening,[],[f34])).
% 2.96/1.00  
% 2.96/1.00  fof(f44,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/1.00    inference(nnf_transformation,[],[f35])).
% 2.96/1.00  
% 2.96/1.00  fof(f71,plain,(
% 2.96/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f44])).
% 2.96/1.00  
% 2.96/1.00  fof(f93,plain,(
% 2.96/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/1.00    inference(equality_resolution,[],[f71])).
% 2.96/1.00  
% 2.96/1.00  fof(f83,plain,(
% 2.96/1.00    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f82,plain,(
% 2.96/1.00    v1_funct_1(sK5)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f8,axiom,(
% 2.96/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f25,plain,(
% 2.96/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f8])).
% 2.96/1.00  
% 2.96/1.00  fof(f26,plain,(
% 2.96/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.96/1.00    inference(flattening,[],[f25])).
% 2.96/1.00  
% 2.96/1.00  fof(f64,plain,(
% 2.96/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f26])).
% 2.96/1.00  
% 2.96/1.00  fof(f4,axiom,(
% 2.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f18,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.96/1.00    inference(ennf_transformation,[],[f4])).
% 2.96/1.00  
% 2.96/1.00  fof(f19,plain,(
% 2.96/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.96/1.00    inference(flattening,[],[f18])).
% 2.96/1.00  
% 2.96/1.00  fof(f59,plain,(
% 2.96/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.96/1.00    inference(cnf_transformation,[],[f19])).
% 2.96/1.00  
% 2.96/1.00  fof(f75,plain,(
% 2.96/1.00    ~v2_struct_0(sK2)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f76,plain,(
% 2.96/1.00    v2_pre_topc(sK2)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f77,plain,(
% 2.96/1.00    l1_pre_topc(sK2)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f80,plain,(
% 2.96/1.00    ~v2_struct_0(sK4)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f84,plain,(
% 2.96/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f72,plain,(
% 2.96/1.00    ~v2_struct_0(sK1)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f86,plain,(
% 2.96/1.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f90,plain,(
% 2.96/1.00    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f87,plain,(
% 2.96/1.00    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.96/1.00    inference(cnf_transformation,[],[f52])).
% 2.96/1.00  
% 2.96/1.00  fof(f2,axiom,(
% 2.96/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/1.00  
% 2.96/1.00  fof(f40,plain,(
% 2.96/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.96/1.00    inference(nnf_transformation,[],[f2])).
% 2.96/1.00  
% 2.96/1.00  fof(f56,plain,(
% 2.96/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.96/1.00    inference(cnf_transformation,[],[f40])).
% 2.96/1.00  
% 2.96/1.00  cnf(c_30,negated_conjecture,
% 2.96/1.00      ( m1_pre_topc(sK3,sK1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1911,plain,
% 2.96/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_14,plain,
% 2.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.96/1.00      | ~ m1_pre_topc(X2,X1)
% 2.96/1.00      | ~ m1_pre_topc(X0,X2)
% 2.96/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1921,plain,
% 2.96/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 2.96/1.00      | v2_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_16,plain,
% 2.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.96/1.00      | ~ m1_pre_topc(X2,X0)
% 2.96/1.00      | m1_pre_topc(X2,X1)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1919,plain,
% 2.96/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.96/1.00      | m1_pre_topc(X2,X1) = iProver_top
% 2.96/1.00      | v2_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2058,plain,
% 2.96/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 2.96/1.00      | v2_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(forward_subsumption_resolution,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_1921,c_1919]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4865,plain,
% 2.96/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 2.96/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1911,c_2058]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_36,negated_conjecture,
% 2.96/1.00      ( v2_pre_topc(sK1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_39,plain,
% 2.96/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_35,negated_conjecture,
% 2.96/1.00      ( l1_pre_topc(sK1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_40,plain,
% 2.96/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5657,plain,
% 2.96/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_4865,c_39,c_40,c_3424,c_4471,c_5540]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_28,negated_conjecture,
% 2.96/1.00      ( m1_pre_topc(sK4,sK1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1913,plain,
% 2.96/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4864,plain,
% 2.96/1.00      ( m1_pre_topc(X0,sK4) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top
% 2.96/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1913,c_2058]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5637,plain,
% 2.96/1.00      ( m1_pre_topc(X0,sK4) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_4864,c_39,c_40,c_47,c_3423,c_3794,c_5517]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_0,plain,
% 2.96/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.96/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1931,plain,
% 2.96/1.00      ( X0 = X1
% 2.96/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.96/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5645,plain,
% 2.96/1.00      ( u1_struct_0(X0) = u1_struct_0(sK4)
% 2.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.96/1.00      | r1_tarski(u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_5637,c_1931]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6069,plain,
% 2.96/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK3)
% 2.96/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,sK3) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_5657,c_5645]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_7,plain,
% 2.96/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.96/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1925,plain,
% 2.96/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3423,plain,
% 2.96/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK4) = iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1913,c_1925]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3424,plain,
% 2.96/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1911,c_1925]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_13,plain,
% 2.96/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.96/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4939,plain,
% 2.96/1.00      ( m1_pre_topc(sK3,sK3) | ~ l1_pre_topc(sK3) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4944,plain,
% 2.96/1.00      ( m1_pre_topc(sK3,sK3) = iProver_top
% 2.96/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_4939]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3436,plain,
% 2.96/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_3423,c_40]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5,plain,
% 2.96/1.00      ( ~ l1_pre_topc(X0)
% 2.96/1.00      | ~ v1_pre_topc(X0)
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.96/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1927,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | v1_pre_topc(X0) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3752,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4
% 2.96/1.00      | v1_pre_topc(sK4) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_3436,c_1927]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_31,negated_conjecture,
% 2.96/1.00      ( ~ v2_struct_0(sK3) ),
% 2.96/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_44,plain,
% 2.96/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_24,negated_conjecture,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
% 2.96/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_8,plain,
% 2.96/1.00      ( v2_struct_0(X0)
% 2.96/1.00      | ~ l1_pre_topc(X0)
% 2.96/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.96/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1924,plain,
% 2.96/1.00      ( v2_struct_0(X0) = iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3668,plain,
% 2.96/1.00      ( v2_struct_0(sK3) = iProver_top
% 2.96/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.96/1.00      | v1_pre_topc(sK4) = iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_24,c_1924]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4994,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK4 ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_3752,c_40,c_44,c_3424,c_3668]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_10,plain,
% 2.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.96/1.00      | m1_pre_topc(X2,X3)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X3)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X0)
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.96/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_198,plain,
% 2.96/1.00      ( ~ l1_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X3)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | m1_pre_topc(X2,X3)
% 2.96/1.00      | ~ m1_pre_topc(X0,X1)
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_10,c_7]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_199,plain,
% 2.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.96/1.00      | m1_pre_topc(X2,X3)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X3)
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_198]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1903,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
% 2.96/1.00      | m1_pre_topc(X3,X1) != iProver_top
% 2.96/1.00      | m1_pre_topc(X2,X0) = iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3546,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK4
% 2.96/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.96/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | l1_pre_topc(X2) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_24,c_1903]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4019,plain,
% 2.96/1.00      ( l1_pre_topc(X2) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.96/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK4
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_3546,c_40,c_3424]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4020,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK4
% 2.96/1.00      | m1_pre_topc(X0,X2) = iProver_top
% 2.96/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_4019]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4029,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
% 2.96/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,X1) = iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_24,c_4020]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4162,plain,
% 2.96/1.00      ( l1_pre_topc(X1) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,X1) = iProver_top
% 2.96/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4 ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_4029,c_40,c_3424]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4163,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
% 2.96/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,X1) = iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_4162]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4173,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
% 2.96/1.00      | m1_pre_topc(sK3,X0) = iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,sK3) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_24,c_4163]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5001,plain,
% 2.96/1.00      ( m1_pre_topc(sK3,sK3) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,sK4) = iProver_top
% 2.96/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_4994,c_4173]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4030,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK4
% 2.96/1.00      | m1_pre_topc(X0,X1) = iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,sK3) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_24,c_4020]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5000,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
% 2.96/1.00      | m1_pre_topc(sK3,sK3) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,X0) = iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_4994,c_4030]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5810,plain,
% 2.96/1.00      ( l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,X0) = iProver_top
% 2.96/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4 ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_5000,c_40,c_3423,c_3424,c_4944]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5811,plain,
% 2.96/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK4
% 2.96/1.00      | m1_pre_topc(sK4,X0) = iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_5810]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_5819,plain,
% 2.96/1.00      ( m1_pre_topc(sK4,sK3) = iProver_top
% 2.96/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_24,c_5811]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6429,plain,
% 2.96/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK3) ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_6069,c_40,c_3423,c_3424,c_4944,c_5001,c_5819]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_20,negated_conjecture,
% 2.96/1.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
% 2.96/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1917,plain,
% 2.96/1.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_21,negated_conjecture,
% 2.96/1.00      ( sK6 = sK7 ),
% 2.96/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1971,plain,
% 2.96/1.00      ( r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) = iProver_top ),
% 2.96/1.00      inference(light_normalisation,[status(thm)],[c_1917,c_21]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_12,plain,
% 2.96/1.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | ~ v2_pre_topc(X0)
% 2.96/1.00      | ~ l1_pre_topc(X0) ),
% 2.96/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_17,plain,
% 2.96/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.96/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.96/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.96/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.96/1.00      | ~ m1_pre_topc(X4,X5)
% 2.96/1.00      | ~ m1_pre_topc(X0,X5)
% 2.96/1.00      | ~ m1_pre_topc(X4,X0)
% 2.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.96/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.96/1.00      | ~ v1_funct_1(X2)
% 2.96/1.00      | v2_struct_0(X5)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X4)
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | ~ v2_pre_topc(X5)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X5)
% 2.96/1.00      | ~ l1_pre_topc(X1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_26,negated_conjecture,
% 2.96/1.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.96/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_554,plain,
% 2.96/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.96/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.96/1.00      | ~ m1_connsp_2(X6,X0,X3)
% 2.96/1.00      | ~ m1_pre_topc(X4,X5)
% 2.96/1.00      | ~ m1_pre_topc(X0,X5)
% 2.96/1.00      | ~ m1_pre_topc(X4,X0)
% 2.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.96/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.96/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.96/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.96/1.00      | ~ v1_funct_1(X2)
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X5)
% 2.96/1.00      | v2_struct_0(X4)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X5)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X5)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.96/1.00      | sK5 != X2 ),
% 2.96/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_555,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.96/1.00      | ~ m1_pre_topc(X0,X2)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.96/1.00      | ~ v1_funct_1(sK5)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(unflattening,[status(thm)],[c_554]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_27,negated_conjecture,
% 2.96/1.00      ( v1_funct_1(sK5) ),
% 2.96/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_559,plain,
% 2.96/1.00      ( ~ r1_tarski(X5,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X2)
% 2.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_555,c_27]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_560,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.96/1.00      | ~ m1_pre_topc(X0,X2)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_559]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_607,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_connsp_2(X5,X3,X4)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(forward_subsumption_resolution,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_560,c_16]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_652,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(X7,u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X6)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | ~ v2_pre_topc(X6)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X6)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | X3 != X6
% 2.96/1.00      | X4 != X5
% 2.96/1.00      | sK0(X6,X5) != X7
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_607]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_653,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(sK0(X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ v2_pre_topc(X3)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X3)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(unflattening,[status(thm)],[c_652]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_11,plain,
% 2.96/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_631,plain,
% 2.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.96/1.00      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X3)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X3)
% 2.96/1.00      | X3 != X1
% 2.96/1.00      | X2 != X0
% 2.96/1.00      | sK0(X3,X2) != X4 ),
% 2.96/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_632,plain,
% 2.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.96/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X1) ),
% 2.96/1.00      inference(unflattening,[status(thm)],[c_631]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_678,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ v2_pre_topc(X3)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X3)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(forward_subsumption_resolution,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_653,c_632]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6,plain,
% 2.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | v2_pre_topc(X0)
% 2.96/1.00      | ~ l1_pre_topc(X1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_699,plain,
% 2.96/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.96/1.00      | r1_tmap_1(X3,X1,sK5,X4)
% 2.96/1.00      | ~ m1_pre_topc(X3,X2)
% 2.96/1.00      | ~ m1_pre_topc(X0,X3)
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.96/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.96/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.96/1.00      | ~ r1_tarski(sK0(X3,X4),u1_struct_0(X0))
% 2.96/1.00      | v2_struct_0(X0)
% 2.96/1.00      | v2_struct_0(X1)
% 2.96/1.00      | v2_struct_0(X3)
% 2.96/1.00      | v2_struct_0(X2)
% 2.96/1.00      | ~ v2_pre_topc(X1)
% 2.96/1.00      | ~ v2_pre_topc(X2)
% 2.96/1.00      | ~ l1_pre_topc(X1)
% 2.96/1.00      | ~ l1_pre_topc(X2)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X3) != u1_struct_0(sK4) ),
% 2.96/1.00      inference(forward_subsumption_resolution,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_678,c_7,c_6]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1901,plain,
% 2.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK2)
% 2.96/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 2.96/1.00      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK5),X4) != iProver_top
% 2.96/1.00      | r1_tmap_1(X1,X0,sK5,X4) = iProver_top
% 2.96/1.00      | m1_pre_topc(X1,X3) != iProver_top
% 2.96/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 2.96/1.00      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.96/1.00      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(X1,X4),u1_struct_0(X2)) != iProver_top
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_struct_0(X2) = iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | v2_struct_0(X3) = iProver_top
% 2.96/1.00      | v2_pre_topc(X0) != iProver_top
% 2.96/1.00      | v2_pre_topc(X3) != iProver_top
% 2.96/1.00      | l1_pre_topc(X0) != iProver_top
% 2.96/1.00      | l1_pre_topc(X3) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2838,plain,
% 2.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.96/1.00      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.96/1.00      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.96/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_struct_0(X2) = iProver_top
% 2.96/1.00      | v2_struct_0(sK2) = iProver_top
% 2.96/1.00      | v2_pre_topc(X2) != iProver_top
% 2.96/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.96/1.00      | l1_pre_topc(X2) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.96/1.00      inference(equality_resolution,[status(thm)],[c_1901]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_34,negated_conjecture,
% 2.96/1.00      ( ~ v2_struct_0(sK2) ),
% 2.96/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_41,plain,
% 2.96/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_33,negated_conjecture,
% 2.96/1.00      ( v2_pre_topc(sK2) ),
% 2.96/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_42,plain,
% 2.96/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_32,negated_conjecture,
% 2.96/1.00      ( l1_pre_topc(sK2) ),
% 2.96/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_43,plain,
% 2.96/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2965,plain,
% 2.96/1.00      ( l1_pre_topc(X2) != iProver_top
% 2.96/1.00      | v2_struct_0(X2) = iProver_top
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.96/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/1.00      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.96/1.00      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.96/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.96/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_2838,c_41,c_42,c_43]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2966,plain,
% 2.96/1.00      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.96/1.00      | r1_tmap_1(X1,sK2,k3_tmap_1(X2,sK2,X0,X1,sK5),X3) != iProver_top
% 2.96/1.00      | r1_tmap_1(X0,sK2,sK5,X3) = iProver_top
% 2.96/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 2.96/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 2.96/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(X0,X3),u1_struct_0(X1)) != iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_struct_0(X2) = iProver_top
% 2.96/1.00      | v2_pre_topc(X2) != iProver_top
% 2.96/1.00      | l1_pre_topc(X2) != iProver_top ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_2965]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2983,plain,
% 2.96/1.00      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.96/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.96/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_struct_0(sK4) = iProver_top
% 2.96/1.00      | v2_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(equality_resolution,[status(thm)],[c_2966]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_29,negated_conjecture,
% 2.96/1.00      ( ~ v2_struct_0(sK4) ),
% 2.96/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_46,plain,
% 2.96/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_25,negated_conjecture,
% 2.96/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.96/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_50,plain,
% 2.96/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3311,plain,
% 2.96/1.00      ( v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.96/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.96/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.96/1.00      | v2_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_2983,c_46,c_50]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3312,plain,
% 2.96/1.00      ( r1_tmap_1(X0,sK2,k3_tmap_1(X1,sK2,sK4,X0,sK5),X2) != iProver_top
% 2.96/1.00      | r1_tmap_1(sK4,sK2,sK5,X2) = iProver_top
% 2.96/1.00      | m1_pre_topc(X0,sK4) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,X1) != iProver_top
% 2.96/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,X2),u1_struct_0(X0)) != iProver_top
% 2.96/1.00      | v2_struct_0(X1) = iProver_top
% 2.96/1.00      | v2_struct_0(X0) = iProver_top
% 2.96/1.00      | v2_pre_topc(X1) != iProver_top
% 2.96/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.96/1.00      inference(renaming,[status(thm)],[c_3311]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3328,plain,
% 2.96/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK6) = iProver_top
% 2.96/1.00      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.96/1.00      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.96/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.96/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top
% 2.96/1.00      | v2_struct_0(sK1) = iProver_top
% 2.96/1.00      | v2_struct_0(sK3) = iProver_top
% 2.96/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/1.00      inference(superposition,[status(thm)],[c_1971,c_3312]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_37,negated_conjecture,
% 2.96/1.00      ( ~ v2_struct_0(sK1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_38,plain,
% 2.96/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_47,plain,
% 2.96/1.00      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_23,negated_conjecture,
% 2.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.96/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_51,plain,
% 2.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_19,negated_conjecture,
% 2.96/1.00      ( ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
% 2.96/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_54,plain,
% 2.96/1.00      ( r1_tmap_1(sK4,sK2,sK5,sK6) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_22,negated_conjecture,
% 2.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.96/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1916,plain,
% 2.96/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_1958,plain,
% 2.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.96/1.00      inference(light_normalisation,[status(thm)],[c_1916,c_21]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3352,plain,
% 2.96/1.00      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
% 2.96/1.00      inference(global_propositional_subsumption,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_3328,c_38,c_39,c_40,c_44,c_47,c_51,c_54,c_1958]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_6434,plain,
% 2.96/1.00      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 2.96/1.00      inference(demodulation,[status(thm)],[c_6429,c_3352]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4,plain,
% 2.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.96/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2674,plain,
% 2.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/1.00      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4195,plain,
% 2.96/1.00      ( ~ m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/1.00      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_2674]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_4196,plain,
% 2.96/1.00      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.96/1.00      | r1_tarski(sK0(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_4195]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2703,plain,
% 2.96/1.00      ( ~ m1_pre_topc(sK4,X0)
% 2.96/1.00      | ~ v2_pre_topc(X0)
% 2.96/1.00      | v2_pre_topc(sK4)
% 2.96/1.00      | ~ l1_pre_topc(X0) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3793,plain,
% 2.96/1.00      ( ~ m1_pre_topc(sK4,sK1)
% 2.96/1.00      | ~ v2_pre_topc(sK1)
% 2.96/1.00      | v2_pre_topc(sK4)
% 2.96/1.00      | ~ l1_pre_topc(sK1) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_2703]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_3794,plain,
% 2.96/1.00      ( m1_pre_topc(sK4,sK1) != iProver_top
% 2.96/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.96/1.00      | v2_pre_topc(sK4) = iProver_top
% 2.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_3793]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2265,plain,
% 2.96/1.00      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.96/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.96/1.00      | v2_struct_0(sK4)
% 2.96/1.00      | ~ v2_pre_topc(sK4)
% 2.96/1.00      | ~ l1_pre_topc(sK4) ),
% 2.96/1.00      inference(instantiation,[status(thm)],[c_632]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(c_2266,plain,
% 2.96/1.00      ( m1_subset_1(sK0(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.96/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.96/1.00      | v2_struct_0(sK4) = iProver_top
% 2.96/1.00      | v2_pre_topc(sK4) != iProver_top
% 2.96/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 2.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2265]) ).
% 2.96/1.00  
% 2.96/1.00  cnf(contradiction,plain,
% 2.96/1.00      ( $false ),
% 2.96/1.00      inference(minisat,
% 2.96/1.00                [status(thm)],
% 2.96/1.00                [c_6434,c_5001,c_4944,c_4196,c_3794,c_3424,c_3423,c_2266,
% 2.96/1.00                 c_51,c_47,c_46,c_40,c_39]) ).
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.96/1.00  
% 2.96/1.00  ------                               Statistics
% 2.96/1.00  
% 2.96/1.00  ------ General
% 2.96/1.00  
% 2.96/1.00  abstr_ref_over_cycles:                  0
% 2.96/1.00  abstr_ref_under_cycles:                 0
% 2.96/1.00  gc_basic_clause_elim:                   0
% 2.96/1.00  forced_gc_time:                         0
% 2.96/1.00  parsing_time:                           0.012
% 2.96/1.00  unif_index_cands_time:                  0.
% 2.96/1.00  unif_index_add_time:                    0.
% 2.96/1.00  orderings_time:                         0.
% 2.96/1.00  out_proof_time:                         0.016
% 2.96/1.00  total_time:                             0.268
% 2.96/1.00  num_of_symbols:                         56
% 2.96/1.00  num_of_terms:                           3720
% 2.96/1.00  
% 2.96/1.00  ------ Preprocessing
% 2.96/1.00  
% 2.96/1.00  num_of_splits:                          0
% 2.96/1.00  num_of_split_atoms:                     0
% 2.96/1.00  num_of_reused_defs:                     0
% 2.96/1.00  num_eq_ax_congr_red:                    8
% 2.96/1.00  num_of_sem_filtered_clauses:            1
% 2.96/1.00  num_of_subtypes:                        0
% 2.96/1.00  monotx_restored_types:                  0
% 2.96/1.00  sat_num_of_epr_types:                   0
% 2.96/1.00  sat_num_of_non_cyclic_types:            0
% 2.96/1.00  sat_guarded_non_collapsed_types:        0
% 2.96/1.00  num_pure_diseq_elim:                    0
% 2.96/1.00  simp_replaced_by:                       0
% 2.96/1.00  res_preprocessed:                       172
% 2.96/1.00  prep_upred:                             0
% 2.96/1.00  prep_unflattend:                        13
% 2.96/1.00  smt_new_axioms:                         0
% 2.96/1.00  pred_elim_cands:                        8
% 2.96/1.00  pred_elim:                              3
% 2.96/1.00  pred_elim_cl:                           3
% 2.96/1.00  pred_elim_cycles:                       6
% 2.96/1.00  merged_defs:                            8
% 2.96/1.00  merged_defs_ncl:                        0
% 2.96/1.00  bin_hyper_res:                          8
% 2.96/1.00  prep_cycles:                            4
% 2.96/1.00  pred_elim_time:                         0.018
% 2.96/1.00  splitting_time:                         0.
% 2.96/1.00  sem_filter_time:                        0.
% 2.96/1.00  monotx_time:                            0.001
% 2.96/1.00  subtype_inf_time:                       0.
% 2.96/1.00  
% 2.96/1.00  ------ Problem properties
% 2.96/1.00  
% 2.96/1.00  clauses:                                34
% 2.96/1.00  conjectures:                            17
% 2.96/1.00  epr:                                    18
% 2.96/1.00  horn:                                   30
% 2.96/1.00  ground:                                 17
% 2.96/1.00  unary:                                  18
% 2.96/1.00  binary:                                 3
% 2.96/1.00  lits:                                   108
% 2.96/1.00  lits_eq:                                10
% 2.96/1.00  fd_pure:                                0
% 2.96/1.00  fd_pseudo:                              0
% 2.96/1.00  fd_cond:                                0
% 2.96/1.00  fd_pseudo_cond:                         1
% 2.96/1.00  ac_symbols:                             0
% 2.96/1.00  
% 2.96/1.00  ------ Propositional Solver
% 2.96/1.00  
% 2.96/1.00  prop_solver_calls:                      27
% 2.96/1.00  prop_fast_solver_calls:                 1712
% 2.96/1.00  smt_solver_calls:                       0
% 2.96/1.00  smt_fast_solver_calls:                  0
% 2.96/1.00  prop_num_of_clauses:                    1881
% 2.96/1.00  prop_preprocess_simplified:             6294
% 2.96/1.00  prop_fo_subsumed:                       70
% 2.96/1.00  prop_solver_time:                       0.
% 2.96/1.00  smt_solver_time:                        0.
% 2.96/1.00  smt_fast_solver_time:                   0.
% 2.96/1.00  prop_fast_solver_time:                  0.
% 2.96/1.00  prop_unsat_core_time:                   0.
% 2.96/1.00  
% 2.96/1.00  ------ QBF
% 2.96/1.00  
% 2.96/1.00  qbf_q_res:                              0
% 2.96/1.00  qbf_num_tautologies:                    0
% 2.96/1.00  qbf_prep_cycles:                        0
% 2.96/1.00  
% 2.96/1.00  ------ BMC1
% 2.96/1.00  
% 2.96/1.00  bmc1_current_bound:                     -1
% 2.96/1.00  bmc1_last_solved_bound:                 -1
% 2.96/1.00  bmc1_unsat_core_size:                   -1
% 2.96/1.00  bmc1_unsat_core_parents_size:           -1
% 2.96/1.00  bmc1_merge_next_fun:                    0
% 2.96/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.96/1.00  
% 2.96/1.00  ------ Instantiation
% 2.96/1.00  
% 2.96/1.00  inst_num_of_clauses:                    556
% 2.96/1.00  inst_num_in_passive:                    61
% 2.96/1.00  inst_num_in_active:                     363
% 2.96/1.00  inst_num_in_unprocessed:                136
% 2.96/1.00  inst_num_of_loops:                      390
% 2.96/1.00  inst_num_of_learning_restarts:          0
% 2.96/1.00  inst_num_moves_active_passive:          23
% 2.96/1.00  inst_lit_activity:                      0
% 2.96/1.00  inst_lit_activity_moves:                0
% 2.96/1.00  inst_num_tautologies:                   0
% 2.96/1.00  inst_num_prop_implied:                  0
% 2.96/1.00  inst_num_existing_simplified:           0
% 2.96/1.00  inst_num_eq_res_simplified:             0
% 2.96/1.00  inst_num_child_elim:                    0
% 2.96/1.00  inst_num_of_dismatching_blockings:      230
% 2.96/1.00  inst_num_of_non_proper_insts:           892
% 2.96/1.00  inst_num_of_duplicates:                 0
% 2.96/1.00  inst_inst_num_from_inst_to_res:         0
% 2.96/1.00  inst_dismatching_checking_time:         0.
% 2.96/1.00  
% 2.96/1.00  ------ Resolution
% 2.96/1.00  
% 2.96/1.00  res_num_of_clauses:                     0
% 2.96/1.00  res_num_in_passive:                     0
% 2.96/1.00  res_num_in_active:                      0
% 2.96/1.00  res_num_of_loops:                       176
% 2.96/1.00  res_forward_subset_subsumed:            109
% 2.96/1.00  res_backward_subset_subsumed:           10
% 2.96/1.00  res_forward_subsumed:                   0
% 2.96/1.00  res_backward_subsumed:                  0
% 2.96/1.00  res_forward_subsumption_resolution:     8
% 2.96/1.00  res_backward_subsumption_resolution:    0
% 2.96/1.00  res_clause_to_clause_subsumption:       518
% 2.96/1.00  res_orphan_elimination:                 0
% 2.96/1.00  res_tautology_del:                      137
% 2.96/1.00  res_num_eq_res_simplified:              0
% 2.96/1.00  res_num_sel_changes:                    0
% 2.96/1.00  res_moves_from_active_to_pass:          0
% 2.96/1.00  
% 2.96/1.00  ------ Superposition
% 2.96/1.00  
% 2.96/1.00  sup_time_total:                         0.
% 2.96/1.00  sup_time_generating:                    0.
% 2.96/1.00  sup_time_sim_full:                      0.
% 2.96/1.00  sup_time_sim_immed:                     0.
% 2.96/1.00  
% 2.96/1.00  sup_num_of_clauses:                     86
% 2.96/1.00  sup_num_in_active:                      72
% 2.96/1.00  sup_num_in_passive:                     14
% 2.96/1.00  sup_num_of_loops:                       77
% 2.96/1.00  sup_fw_superposition:                   63
% 2.96/1.00  sup_bw_superposition:                   47
% 2.96/1.00  sup_immediate_simplified:               22
% 2.96/1.00  sup_given_eliminated:                   0
% 2.96/1.00  comparisons_done:                       0
% 2.96/1.00  comparisons_avoided:                    0
% 2.96/1.00  
% 2.96/1.00  ------ Simplifications
% 2.96/1.00  
% 2.96/1.00  
% 2.96/1.00  sim_fw_subset_subsumed:                 18
% 2.96/1.00  sim_bw_subset_subsumed:                 6
% 2.96/1.00  sim_fw_subsumed:                        4
% 2.96/1.00  sim_bw_subsumed:                        0
% 2.96/1.00  sim_fw_subsumption_res:                 2
% 2.96/1.00  sim_bw_subsumption_res:                 0
% 2.96/1.00  sim_tautology_del:                      17
% 2.96/1.00  sim_eq_tautology_del:                   4
% 2.96/1.00  sim_eq_res_simp:                        0
% 2.96/1.00  sim_fw_demodulated:                     0
% 2.96/1.00  sim_bw_demodulated:                     5
% 2.96/1.00  sim_light_normalised:                   3
% 2.96/1.00  sim_joinable_taut:                      0
% 2.96/1.00  sim_joinable_simp:                      0
% 2.96/1.00  sim_ac_normalised:                      0
% 2.96/1.00  sim_smt_subsumption:                    0
% 2.96/1.00  
%------------------------------------------------------------------------------
