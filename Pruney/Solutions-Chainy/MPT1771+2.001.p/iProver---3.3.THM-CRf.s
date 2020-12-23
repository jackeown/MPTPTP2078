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
% DateTime   : Thu Dec  3 12:23:05 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_7416)

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
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f48,f47,f46,f45,f44,f43,f42])).

fof(f85,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f5,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_451,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_6943,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_450,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_6988,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6943,c_450])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_443,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_6936,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_447,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_6940,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_456,plain,
    ( m1_pre_topc(X0_51,X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_6923,plain,
    ( m1_pre_topc(X0_51,X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_446,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_6939,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_463,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6916,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_453,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | m1_pre_topc(X2_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_6926,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_7210,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6916,c_6926])).

cnf(c_8719,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6939,c_7210])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_47,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_48,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8880,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8719,c_40,c_41,c_42,c_47,c_48])).

cnf(c_8881,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_8880])).

cnf(c_8892,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_51,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK0,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6936,c_8881])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6915,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_8152,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6939,c_6915])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8563,plain,
    ( m1_pre_topc(X0_51,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8152,c_37,c_38,c_39,c_40,c_41,c_42,c_47,c_48,c_49,c_7416])).

cnf(c_8564,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51)
    | m1_pre_topc(X0_51,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8563])).

cnf(c_8571,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_6936,c_8564])).

cnf(c_8924,plain,
    ( k3_tmap_1(X0_51,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK0,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8892,c_8571])).

cnf(c_8957,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6923,c_8924])).

cnf(c_62,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_64,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_8937,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8924])).

cnf(c_9081,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8957,c_37,c_38,c_39,c_64,c_8937])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_459,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_6920,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_9084,plain,
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
    inference(superposition,[status(thm)],[c_9081,c_6920])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9650,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9084,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_47,c_48,c_49,c_64])).

cnf(c_9655,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9650,c_7210])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_6921,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_9085,plain,
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
    inference(superposition,[status(thm)],[c_9081,c_6921])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_6922,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_8225,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6939,c_6922])).

cnf(c_8612,plain,
    ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8225,c_40,c_41,c_42,c_47,c_48])).

cnf(c_8613,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK0,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8612])).

cnf(c_9086,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9081,c_8613])).

cnf(c_10832,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9655,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_47,c_48,c_49,c_64,c_9085,c_9086])).

cnf(c_10833,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_10832])).

cnf(c_10844,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(X0_51,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | m1_pre_topc(sK3,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6940,c_10833])).

cnf(c_9657,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9650,c_6915])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_466,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3632,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_3633,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3632])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_468,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3631,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_3635,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3631])).

cnf(c_10634,plain,
    ( m1_pre_topc(X0_51,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9657,c_37,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_47,c_48,c_49,c_64,c_3633,c_3635,c_9085,c_9086])).

cnf(c_10635,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51)
    | m1_pre_topc(X0_51,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10634])).

cnf(c_10642,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_6940,c_10635])).

cnf(c_10864,plain,
    ( k3_tmap_1(X0_51,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | m1_pre_topc(sK3,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10844,c_10642])).

cnf(c_10883,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6936,c_10864])).

cnf(c_10874,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10864])).

cnf(c_10904,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10883,c_37,c_38,c_39,c_46,c_10874])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_441,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_6934,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_8893,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_51,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK0,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6934,c_8881])).

cnf(c_8572,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_6934,c_8564])).

cnf(c_8913,plain,
    ( k3_tmap_1(X0_51,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK0,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8893,c_8572])).

cnf(c_8949,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6923,c_8913])).

cnf(c_8934,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8913])).

cnf(c_8983,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8949,c_37,c_38,c_39,c_64,c_8934])).

cnf(c_16,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_454,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k3_tmap_1(X2_51,X1_51,X4_51,X3_51,X0_52)),k3_tmap_1(X2_51,X1_51,X4_51,X0_51,X0_52))
    | ~ v1_funct_2(X0_52,u1_struct_0(X4_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_pre_topc(X3_51,X4_51)
    | ~ m1_pre_topc(X4_51,X2_51)
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_51),u1_struct_0(X1_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X4_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_6925,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k3_tmap_1(X2_51,X1_51,X4_51,X3_51,X0_52)),k3_tmap_1(X2_51,X1_51,X4_51,X0_51,X0_52)) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X4_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X4_51) != iProver_top
    | m1_pre_topc(X4_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X4_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_7271,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k3_tmap_1(X2_51,X1_51,X4_51,X3_51,X0_52)),k3_tmap_1(X2_51,X1_51,X4_51,X0_51,X0_52)) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X4_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X3_51,X4_51) != iProver_top
    | m1_pre_topc(X4_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X4_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6925,c_6926])).

cnf(c_9844,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3)),k3_tmap_1(sK0,sK1,sK0,X0_51,sK4)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(X0_51,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9081,c_7271])).

cnf(c_3440,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_3430,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_3812,plain,
    ( m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(X0_51,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3440,c_3430])).

cnf(c_3898,plain,
    ( m1_pre_topc(X0_51,sK3) != iProver_top
    | m1_pre_topc(X0_51,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3812,c_38,c_39])).

cnf(c_10180,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3)),k3_tmap_1(sK0,sK1,sK0,X0_51,sK4)) = iProver_top
    | m1_pre_topc(X0_51,sK3) != iProver_top
    | v2_struct_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9844,c_37,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_47,c_48,c_49,c_64,c_3812])).

cnf(c_10190,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8983,c_10180])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_50,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10227,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10190,c_43,c_50])).

cnf(c_10907,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10904,c_10227])).

cnf(c_10911,plain,
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
    inference(superposition,[status(thm)],[c_10904,c_6920])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11118,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10911,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_46,c_47,c_48,c_49,c_64,c_9084,c_9085,c_9086])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_469,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
    | ~ v1_funct_2(X1_52,X0_53,X1_53)
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | X0_52 = X1_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6910,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X0_53,X1_53,X0_52,X1_52) != iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_11127,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11118,c_6910])).

cnf(c_10912,plain,
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
    inference(superposition,[status(thm)],[c_10904,c_6921])).

cnf(c_9656,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9650,c_6922])).

cnf(c_10591,plain,
    ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9656,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_47,c_48,c_49,c_64,c_9085,c_9086])).

cnf(c_10592,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK3,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10591])).

cnf(c_10913,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10904,c_10592])).

cnf(c_11456,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11127,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_46,c_47,c_48,c_49,c_64,c_9084,c_9085,c_9086,c_10912,c_10913])).

cnf(c_11457,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_11456])).

cnf(c_11468,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10907,c_11457])).

cnf(c_3603,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_3604,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3603])).

cnf(c_3,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_467,plain,
    ( l1_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_7343,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_7344,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7343])).

cnf(c_7603,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_7604,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7603])).

cnf(c_6913,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_7543,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6936,c_6913])).

cnf(c_7620,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7543,c_39,c_46,c_3633])).

cnf(c_6912,plain,
    ( l1_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_7625,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7620,c_6912])).

cnf(c_8986,plain,
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
    inference(superposition,[status(thm)],[c_8983,c_6920])).

cnf(c_8987,plain,
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
    inference(superposition,[status(thm)],[c_8983,c_6921])).

cnf(c_8988,plain,
    ( m1_pre_topc(sK0,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8983,c_8613])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_462,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | m1_subset_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | ~ l1_struct_0(X2_51)
    | ~ l1_struct_0(X1_51)
    | ~ l1_struct_0(X0_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6917,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) = iProver_top
    | l1_struct_0(X2_51) != iProver_top
    | l1_struct_0(X1_51) != iProver_top
    | l1_struct_0(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_7839,plain,
    ( k2_tmap_1(X0_51,X1_51,X0_52,X2_51) = X1_52
    | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | l1_struct_0(X2_51) != iProver_top
    | l1_struct_0(X1_51) != iProver_top
    | l1_struct_0(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6917,c_6910])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ l1_struct_0(X2_51)
    | ~ l1_struct_0(X1_51)
    | ~ l1_struct_0(X0_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_507,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | l1_struct_0(X2_51) != iProver_top
    | l1_struct_0(X1_51) != iProver_top
    | l1_struct_0(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ l1_struct_0(X2_51)
    | ~ l1_struct_0(X1_51)
    | ~ l1_struct_0(X0_51)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_510,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | l1_struct_0(X2_51) != iProver_top
    | l1_struct_0(X1_51) != iProver_top
    | l1_struct_0(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_10310,plain,
    ( v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | l1_struct_0(X0_51) != iProver_top
    | l1_struct_0(X1_51) != iProver_top
    | l1_struct_0(X2_51) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | k2_tmap_1(X0_51,X1_51,X0_52,X2_51) = X1_52
    | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7839,c_507,c_510])).

cnf(c_10311,plain,
    ( k2_tmap_1(X0_51,X1_51,X0_52,X2_51) = X1_52
    | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | l1_struct_0(X2_51) != iProver_top
    | l1_struct_0(X1_51) != iProver_top
    | l1_struct_0(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_10310])).

cnf(c_11079,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10907,c_10311])).

cnf(c_11480,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11468,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_46,c_47,c_48,c_49,c_64,c_3604,c_7344,c_7604,c_7625,c_8986,c_8987,c_8988,c_9084,c_9085,c_9086,c_11079])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f88])).

cnf(c_455,plain,
    ( ~ r1_tmap_1(X0_51,X1_51,X0_52,X1_52)
    | r1_tmap_1(X2_51,X1_51,k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52)
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X1_52,u1_struct_0(X2_51))
    | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X2_51)
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_6924,plain,
    ( r1_tmap_1(X0_51,X1_51,X0_52,X1_52) != iProver_top
    | r1_tmap_1(X2_51,X1_51,k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_465,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | m1_subset_1(X0_52,u1_struct_0(X1_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_6914,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_7238,plain,
    ( r1_tmap_1(X0_51,X1_51,X0_52,X1_52) != iProver_top
    | r1_tmap_1(X2_51,X1_51,k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(X2_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6924,c_6914])).

cnf(c_11536,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_52) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_52) = iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11480,c_7238])).

cnf(c_12541,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_52) = iProver_top
    | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11536,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,c_47,c_48,c_49,c_50,c_64,c_3633,c_3635,c_9084,c_9085,c_9086])).

cnf(c_12542,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_52) != iProver_top
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12541])).

cnf(c_12551,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6988,c_12542])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_54,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12551,c_54,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.56/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.49  
% 7.56/1.49  ------  iProver source info
% 7.56/1.49  
% 7.56/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.49  git: non_committed_changes: false
% 7.56/1.49  git: last_make_outside_of_git: false
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  ------ Parsing...
% 7.56/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  ------ Proving...
% 7.56/1.49  ------ Problem Properties 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  clauses                                 37
% 7.56/1.49  conjectures                             19
% 7.56/1.49  EPR                                     18
% 7.56/1.49  Horn                                    29
% 7.56/1.49  unary                                   19
% 7.56/1.49  binary                                  2
% 7.56/1.49  lits                                    167
% 7.56/1.49  lits eq                                 4
% 7.56/1.49  fd_pure                                 0
% 7.56/1.49  fd_pseudo                               0
% 7.56/1.49  fd_cond                                 0
% 7.56/1.49  fd_pseudo_cond                          1
% 7.56/1.49  AC symbols                              0
% 7.56/1.49  
% 7.56/1.49  ------ Input Options Time Limit: Unbounded
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing...
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.56/1.49  Current options:
% 7.56/1.49  ------ 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing...
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS status Theorem for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  fof(f14,conjecture,(
% 7.56/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f15,negated_conjecture,(
% 7.56/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 7.56/1.49    inference(negated_conjecture,[],[f14])).
% 7.56/1.49  
% 7.56/1.49  fof(f39,plain,(
% 7.56/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.56/1.49    inference(ennf_transformation,[],[f15])).
% 7.56/1.49  
% 7.56/1.49  fof(f40,plain,(
% 7.56/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.56/1.49    inference(flattening,[],[f39])).
% 7.56/1.49  
% 7.56/1.49  fof(f48,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),sK6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f47,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f46,plain,(
% 7.56/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f45,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f44,plain,(
% 7.56/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,X1,k2_tmap_1(X0,X1,X4,sK2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f43,plain,(
% 7.56/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(X0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f42,plain,(
% 7.56/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f49,plain,(
% 7.56/1.49    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f48,f47,f46,f45,f44,f43,f42])).
% 7.56/1.49  
% 7.56/1.49  fof(f85,plain,(
% 7.56/1.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f84,plain,(
% 7.56/1.49    sK5 = sK6),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f77,plain,(
% 7.56/1.49    m1_pre_topc(sK3,sK0)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f81,plain,(
% 7.56/1.49    m1_pre_topc(sK2,sK3)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f10,axiom,(
% 7.56/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f32,plain,(
% 7.56/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.56/1.49    inference(ennf_transformation,[],[f10])).
% 7.56/1.49  
% 7.56/1.49  fof(f64,plain,(
% 7.56/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f32])).
% 7.56/1.49  
% 7.56/1.49  fof(f80,plain,(
% 7.56/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f7,axiom,(
% 7.56/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f26,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.56/1.49    inference(ennf_transformation,[],[f7])).
% 7.56/1.49  
% 7.56/1.49  fof(f27,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.56/1.49    inference(flattening,[],[f26])).
% 7.56/1.49  
% 7.56/1.49  fof(f57,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f27])).
% 7.56/1.49  
% 7.56/1.49  fof(f13,axiom,(
% 7.56/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f37,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.56/1.49    inference(ennf_transformation,[],[f13])).
% 7.56/1.49  
% 7.56/1.49  fof(f38,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.56/1.49    inference(flattening,[],[f37])).
% 7.56/1.49  
% 7.56/1.49  fof(f67,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f38])).
% 7.56/1.49  
% 7.56/1.49  fof(f71,plain,(
% 7.56/1.49    ~v2_struct_0(sK1)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f72,plain,(
% 7.56/1.49    v2_pre_topc(sK1)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f73,plain,(
% 7.56/1.49    l1_pre_topc(sK1)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f78,plain,(
% 7.56/1.49    v1_funct_1(sK4)),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f79,plain,(
% 7.56/1.49    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.56/1.49    inference(cnf_transformation,[],[f49])).
% 7.56/1.49  
% 7.56/1.49  fof(f6,axiom,(
% 7.56/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f24,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f6])).
% 7.56/1.50  
% 7.56/1.50  fof(f25,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.56/1.50    inference(flattening,[],[f24])).
% 7.56/1.50  
% 7.56/1.50  fof(f56,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f25])).
% 7.56/1.50  
% 7.56/1.50  fof(f68,plain,(
% 7.56/1.50    ~v2_struct_0(sK0)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f69,plain,(
% 7.56/1.50    v2_pre_topc(sK0)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f70,plain,(
% 7.56/1.50    l1_pre_topc(sK0)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f9,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f30,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f9])).
% 7.56/1.50  
% 7.56/1.50  fof(f31,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.56/1.50    inference(flattening,[],[f30])).
% 7.56/1.50  
% 7.56/1.50  fof(f63,plain,(
% 7.56/1.50    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f31])).
% 7.56/1.50  
% 7.56/1.50  fof(f62,plain,(
% 7.56/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f31])).
% 7.56/1.50  
% 7.56/1.50  fof(f61,plain,(
% 7.56/1.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f31])).
% 7.56/1.50  
% 7.56/1.50  fof(f76,plain,(
% 7.56/1.50    ~v2_struct_0(sK3)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f4,axiom,(
% 7.56/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f21,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.56/1.50    inference(ennf_transformation,[],[f4])).
% 7.56/1.50  
% 7.56/1.50  fof(f54,plain,(
% 7.56/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f21])).
% 7.56/1.50  
% 7.56/1.50  fof(f2,axiom,(
% 7.56/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f18,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f2])).
% 7.56/1.50  
% 7.56/1.50  fof(f19,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.56/1.50    inference(flattening,[],[f18])).
% 7.56/1.50  
% 7.56/1.50  fof(f52,plain,(
% 7.56/1.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f19])).
% 7.56/1.50  
% 7.56/1.50  fof(f75,plain,(
% 7.56/1.50    m1_pre_topc(sK2,sK0)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f12,axiom,(
% 7.56/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f35,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f12])).
% 7.56/1.50  
% 7.56/1.50  fof(f36,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.56/1.50    inference(flattening,[],[f35])).
% 7.56/1.50  
% 7.56/1.50  fof(f66,plain,(
% 7.56/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f36])).
% 7.56/1.50  
% 7.56/1.50  fof(f74,plain,(
% 7.56/1.50    ~v2_struct_0(sK2)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f1,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f16,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.56/1.50    inference(ennf_transformation,[],[f1])).
% 7.56/1.50  
% 7.56/1.50  fof(f17,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(flattening,[],[f16])).
% 7.56/1.50  
% 7.56/1.50  fof(f41,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.56/1.50    inference(nnf_transformation,[],[f17])).
% 7.56/1.50  
% 7.56/1.50  fof(f50,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f41])).
% 7.56/1.50  
% 7.56/1.50  fof(f3,axiom,(
% 7.56/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f20,plain,(
% 7.56/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.56/1.50    inference(ennf_transformation,[],[f3])).
% 7.56/1.50  
% 7.56/1.50  fof(f53,plain,(
% 7.56/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f20])).
% 7.56/1.50  
% 7.56/1.50  fof(f8,axiom,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f28,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f8])).
% 7.56/1.50  
% 7.56/1.50  fof(f29,plain,(
% 7.56/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 7.56/1.50    inference(flattening,[],[f28])).
% 7.56/1.50  
% 7.56/1.50  fof(f60,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f59,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f58,plain,(
% 7.56/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f29])).
% 7.56/1.50  
% 7.56/1.50  fof(f11,axiom,(
% 7.56/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f33,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f11])).
% 7.56/1.50  
% 7.56/1.50  fof(f34,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.56/1.50    inference(flattening,[],[f33])).
% 7.56/1.50  
% 7.56/1.50  fof(f65,plain,(
% 7.56/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f34])).
% 7.56/1.50  
% 7.56/1.50  fof(f88,plain,(
% 7.56/1.50    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(equality_resolution,[],[f65])).
% 7.56/1.50  
% 7.56/1.50  fof(f5,axiom,(
% 7.56/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.56/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.50  
% 7.56/1.50  fof(f22,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.56/1.50    inference(ennf_transformation,[],[f5])).
% 7.56/1.50  
% 7.56/1.50  fof(f23,plain,(
% 7.56/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.56/1.50    inference(flattening,[],[f22])).
% 7.56/1.50  
% 7.56/1.50  fof(f55,plain,(
% 7.56/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.56/1.50    inference(cnf_transformation,[],[f23])).
% 7.56/1.50  
% 7.56/1.50  fof(f86,plain,(
% 7.56/1.50    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  fof(f83,plain,(
% 7.56/1.50    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.56/1.50    inference(cnf_transformation,[],[f49])).
% 7.56/1.50  
% 7.56/1.50  cnf(c_19,negated_conjecture,
% 7.56/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 7.56/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_451,negated_conjecture,
% 7.56/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_19]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6943,plain,
% 7.56/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_20,negated_conjecture,
% 7.56/1.50      ( sK5 = sK6 ),
% 7.56/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_450,negated_conjecture,
% 7.56/1.50      ( sK5 = sK6 ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_20]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6988,plain,
% 7.56/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK6) = iProver_top ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_6943,c_450]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_27,negated_conjecture,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_443,negated_conjecture,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_27]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6936,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_23,negated_conjecture,
% 7.56/1.50      ( m1_pre_topc(sK2,sK3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_447,negated_conjecture,
% 7.56/1.50      ( m1_pre_topc(sK2,sK3) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6940,plain,
% 7.56/1.50      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_14,plain,
% 7.56/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_456,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X0_51) | ~ l1_pre_topc(X0_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6923,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_24,negated_conjecture,
% 7.56/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.56/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_446,negated_conjecture,
% 7.56/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6939,plain,
% 7.56/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_pre_topc(X3,X4)
% 7.56/1.50      | ~ m1_pre_topc(X3,X1)
% 7.56/1.50      | ~ m1_pre_topc(X1,X4)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | v2_struct_0(X4)
% 7.56/1.50      | v2_struct_0(X2)
% 7.56/1.50      | ~ l1_pre_topc(X4)
% 7.56/1.50      | ~ l1_pre_topc(X2)
% 7.56/1.50      | ~ v2_pre_topc(X4)
% 7.56/1.50      | ~ v2_pre_topc(X2)
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_463,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X2_51,X0_51)
% 7.56/1.50      | ~ m1_pre_topc(X0_51,X3_51)
% 7.56/1.50      | ~ m1_pre_topc(X2_51,X3_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X3_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X3_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X3_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52)
% 7.56/1.50      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6916,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X3_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_17,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.56/1.50      | ~ m1_pre_topc(X2,X0)
% 7.56/1.50      | m1_pre_topc(X2,X1)
% 7.56/1.50      | ~ l1_pre_topc(X1)
% 7.56/1.50      | ~ v2_pre_topc(X1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_453,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.56/1.50      | ~ m1_pre_topc(X2_51,X0_51)
% 7.56/1.50      | m1_pre_topc(X2_51,X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6926,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7210,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X3_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(forward_subsumption_resolution,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_6916,c_6926]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8719,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)
% 7.56/1.50      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6939,c_7210]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_33,negated_conjecture,
% 7.56/1.50      ( ~ v2_struct_0(sK1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_40,plain,
% 7.56/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_32,negated_conjecture,
% 7.56/1.50      ( v2_pre_topc(sK1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_41,plain,
% 7.56/1.50      ( v2_pre_topc(sK1) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_31,negated_conjecture,
% 7.56/1.50      ( l1_pre_topc(sK1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_42,plain,
% 7.56/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_26,negated_conjecture,
% 7.56/1.50      ( v1_funct_1(sK4) ),
% 7.56/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_47,plain,
% 7.56/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_25,negated_conjecture,
% 7.56/1.50      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_48,plain,
% 7.56/1.50      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8880,plain,
% 7.56/1.50      ( l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8719,c_40,c_41,c_42,c_47,c_48]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8881,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_8880]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8892,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0_51,sK1,sK0,sK3,sK4)
% 7.56/1.50      | m1_pre_topc(sK0,X0_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6936,c_8881]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_pre_topc(X3,X1)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | v2_struct_0(X1)
% 7.56/1.50      | v2_struct_0(X2)
% 7.56/1.50      | ~ l1_pre_topc(X1)
% 7.56/1.50      | ~ l1_pre_topc(X2)
% 7.56/1.50      | ~ v2_pre_topc(X1)
% 7.56/1.50      | ~ v2_pre_topc(X2)
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_464,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X2_51,X0_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X0_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X0_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X0_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52)
% 7.56/1.50      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6915,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8152,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51)
% 7.56/1.50      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6939,c_6915]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_36,negated_conjecture,
% 7.56/1.50      ( ~ v2_struct_0(sK0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_37,plain,
% 7.56/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_35,negated_conjecture,
% 7.56/1.50      ( v2_pre_topc(sK0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_38,plain,
% 7.56/1.50      ( v2_pre_topc(sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_34,negated_conjecture,
% 7.56/1.50      ( l1_pre_topc(sK0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_39,plain,
% 7.56/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8563,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,sK0) != iProver_top
% 7.56/1.50      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8152,c_37,c_38,c_39,c_40,c_41,c_42,c_47,c_48,c_49,
% 7.56/1.50                 c_7416]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8564,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_51)) = k2_tmap_1(sK0,sK1,sK4,X0_51)
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_8563]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8571,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6936,c_8564]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8924,plain,
% 7.56/1.50      ( k3_tmap_1(X0_51,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 7.56/1.50      | m1_pre_topc(sK0,X0_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_8892,c_8571]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8957,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6923,c_8924]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_62,plain,
% 7.56/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_64,plain,
% 7.56/1.50      ( m1_pre_topc(sK0,sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_62]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8937,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_8924]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9081,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8957,c_37,c_38,c_39,c_64,c_8937]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_pre_topc(X3,X4)
% 7.56/1.50      | ~ m1_pre_topc(X1,X4)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.56/1.50      | v2_struct_0(X4)
% 7.56/1.50      | v2_struct_0(X2)
% 7.56/1.50      | ~ l1_pre_topc(X4)
% 7.56/1.50      | ~ l1_pre_topc(X2)
% 7.56/1.50      | ~ v2_pre_topc(X4)
% 7.56/1.50      | ~ v2_pre_topc(X2)
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_459,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X0_51,X2_51)
% 7.56/1.50      | ~ m1_pre_topc(X3_51,X2_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X2_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X2_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X2_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6920,plain,
% 7.56/1.50      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | m1_subset_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) = iProver_top
% 7.56/1.50      | v2_struct_0(X3_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9084,plain,
% 7.56/1.50      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 7.56/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9081,c_6920]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_46,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_49,plain,
% 7.56/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9650,plain,
% 7.56/1.50      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_9084,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_47,c_48,
% 7.56/1.50                 c_49,c_64]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9655,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9650,c_7210]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_12,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_pre_topc(X4,X3)
% 7.56/1.50      | ~ m1_pre_topc(X1,X3)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | v2_struct_0(X3)
% 7.56/1.50      | v2_struct_0(X2)
% 7.56/1.50      | ~ l1_pre_topc(X3)
% 7.56/1.50      | ~ l1_pre_topc(X2)
% 7.56/1.50      | ~ v2_pre_topc(X3)
% 7.56/1.50      | ~ v2_pre_topc(X2)
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_458,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X3_51,X2_51)
% 7.56/1.50      | ~ m1_pre_topc(X0_51,X2_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X2_51)
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X2_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X2_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6921,plain,
% 7.56/1.50      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
% 7.56/1.50      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X2_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X2_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X2_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9085,plain,
% 7.56/1.50      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 7.56/1.50      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9081,c_6921]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_13,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_pre_topc(X3,X4)
% 7.56/1.50      | ~ m1_pre_topc(X1,X4)
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | v2_struct_0(X4)
% 7.56/1.50      | v2_struct_0(X2)
% 7.56/1.50      | ~ l1_pre_topc(X4)
% 7.56/1.50      | ~ l1_pre_topc(X2)
% 7.56/1.50      | ~ v2_pre_topc(X4)
% 7.56/1.50      | ~ v2_pre_topc(X2)
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_457,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X0_51,X2_51)
% 7.56/1.50      | ~ m1_pre_topc(X3_51,X2_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X2_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X2_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X2_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52)
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6922,plain,
% 7.56/1.50      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X3_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X3_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8225,plain,
% 7.56/1.50      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)) = iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6939,c_6922]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8612,plain,
% 7.56/1.50      ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8225,c_40,c_41,c_42,c_47,c_48]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8613,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK0,X0_51,sK4)) = iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_8612]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9086,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9081,c_8613]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10832,plain,
% 7.56/1.50      ( l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_9655,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_47,c_48,
% 7.56/1.50                 c_49,c_64,c_9085,c_9086]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10833,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_10832]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10844,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(X0_51,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
% 7.56/1.50      | m1_pre_topc(sK3,X0_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6940,c_10833]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9657,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51)
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | v2_struct_0(sK3) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9650,c_6915]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_28,negated_conjecture,
% 7.56/1.50      ( ~ v2_struct_0(sK3) ),
% 7.56/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_45,plain,
% 7.56/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_4,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_466,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | l1_pre_topc(X0_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3632,plain,
% 7.56/1.50      ( ~ m1_pre_topc(sK3,sK0) | l1_pre_topc(sK3) | ~ l1_pre_topc(sK0) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_466]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3633,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK3) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_3632]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_2,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.56/1.50      | ~ l1_pre_topc(X1)
% 7.56/1.50      | ~ v2_pre_topc(X1)
% 7.56/1.50      | v2_pre_topc(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_468,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | v2_pre_topc(X0_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3631,plain,
% 7.56/1.50      ( ~ m1_pre_topc(sK3,sK0)
% 7.56/1.50      | ~ l1_pre_topc(sK0)
% 7.56/1.50      | v2_pre_topc(sK3)
% 7.56/1.50      | ~ v2_pre_topc(sK0) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_468]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3635,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK3) = iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_3631]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10634,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_9657,c_37,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_47,
% 7.56/1.50                 c_48,c_49,c_64,c_3633,c_3635,c_9085,c_9086]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10635,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(X0_51)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_51)
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_10634]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10642,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6940,c_10635]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10864,plain,
% 7.56/1.50      ( k3_tmap_1(X0_51,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 7.56/1.50      | m1_pre_topc(sK3,X0_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_10844,c_10642]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10883,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6936,c_10864]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10874,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
% 7.56/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_10864]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10904,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_10883,c_37,c_38,c_39,c_46,c_10874]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_29,negated_conjecture,
% 7.56/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_441,negated_conjecture,
% 7.56/1.50      ( m1_pre_topc(sK2,sK0) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_29]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6934,plain,
% 7.56/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8893,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_51,sK1,sK0,sK2,sK4)
% 7.56/1.50      | m1_pre_topc(sK0,X0_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6934,c_8881]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8572,plain,
% 7.56/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6934,c_8564]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8913,plain,
% 7.56/1.50      ( k3_tmap_1(X0_51,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 7.56/1.50      | m1_pre_topc(sK0,X0_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(light_normalisation,[status(thm)],[c_8893,c_8572]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8949,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6923,c_8913]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8934,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_8913]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8983,plain,
% 7.56/1.50      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_8949,c_37,c_38,c_39,c_64,c_8934]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_16,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k3_tmap_1(X2,X1,X4,X3,X5)),k3_tmap_1(X2,X1,X4,X0,X5))
% 7.56/1.50      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
% 7.56/1.50      | ~ m1_pre_topc(X3,X2)
% 7.56/1.50      | ~ m1_pre_topc(X3,X4)
% 7.56/1.50      | ~ m1_pre_topc(X4,X2)
% 7.56/1.50      | ~ m1_pre_topc(X0,X2)
% 7.56/1.50      | ~ m1_pre_topc(X0,X3)
% 7.56/1.50      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
% 7.56/1.50      | v2_struct_0(X2)
% 7.56/1.50      | v2_struct_0(X1)
% 7.56/1.50      | v2_struct_0(X3)
% 7.56/1.50      | v2_struct_0(X0)
% 7.56/1.50      | v2_struct_0(X4)
% 7.56/1.50      | ~ l1_pre_topc(X2)
% 7.56/1.50      | ~ l1_pre_topc(X1)
% 7.56/1.50      | ~ v2_pre_topc(X2)
% 7.56/1.50      | ~ v2_pre_topc(X1)
% 7.56/1.50      | ~ v1_funct_1(X5) ),
% 7.56/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_454,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k3_tmap_1(X2_51,X1_51,X4_51,X3_51,X0_52)),k3_tmap_1(X2_51,X1_51,X4_51,X0_51,X0_52))
% 7.56/1.50      | ~ v1_funct_2(X0_52,u1_struct_0(X4_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X3_51,X2_51)
% 7.56/1.50      | ~ m1_pre_topc(X3_51,X4_51)
% 7.56/1.50      | ~ m1_pre_topc(X4_51,X2_51)
% 7.56/1.50      | ~ m1_pre_topc(X0_51,X2_51)
% 7.56/1.50      | ~ m1_pre_topc(X0_51,X3_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X2_51)
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X3_51)
% 7.56/1.50      | v2_struct_0(X0_51)
% 7.56/1.50      | v2_struct_0(X4_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X2_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X2_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6925,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k3_tmap_1(X2_51,X1_51,X4_51,X3_51,X0_52)),k3_tmap_1(X2_51,X1_51,X4_51,X0_51,X0_52)) = iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X4_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X3_51,X4_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X4_51,X2_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X2_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X3_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X4_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X2_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X2_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7271,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k3_tmap_1(X2_51,X1_51,X3_51,X0_51,k3_tmap_1(X2_51,X1_51,X4_51,X3_51,X0_52)),k3_tmap_1(X2_51,X1_51,X4_51,X0_51,X0_52)) = iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X4_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X3_51,X4_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X4_51,X2_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X2_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X3_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X4_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X2_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X2_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(forward_subsumption_resolution,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_6925,c_6926]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9844,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3)),k3_tmap_1(sK0,sK1,sK0,X0_51,sK4)) = iProver_top
% 7.56/1.50      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | v2_struct_0(sK3) = iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9081,c_7271]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3440,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3430,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3812,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_3440,c_3430]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3898,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK0) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_3812,c_38,c_39]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10180,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3)),k3_tmap_1(sK0,sK1,sK0,X0_51,sK4)) = iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,sK3) != iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_9844,c_37,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_47,
% 7.56/1.50                 c_48,c_49,c_64,c_3812]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10190,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.56/1.50      | v2_struct_0(sK2) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_8983,c_10180]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_30,negated_conjecture,
% 7.56/1.50      ( ~ v2_struct_0(sK2) ),
% 7.56/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_43,plain,
% 7.56/1.50      ( v2_struct_0(sK2) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_50,plain,
% 7.56/1.50      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10227,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_10190,c_43,c_50]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10907,plain,
% 7.56/1.50      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 7.56/1.50      inference(demodulation,[status(thm)],[c_10904,c_10227]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10911,plain,
% 7.56/1.50      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_10904,c_6920]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_44,plain,
% 7.56/1.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11118,plain,
% 7.56/1.50      ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_10911,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_46,c_47,
% 7.56/1.50                 c_48,c_49,c_64,c_9084,c_9085,c_9086]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_1,plain,
% 7.56/1.50      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.56/1.50      | ~ v1_funct_2(X3,X0,X1)
% 7.56/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.56/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.56/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.56/1.50      | ~ v1_funct_1(X3)
% 7.56/1.50      | ~ v1_funct_1(X2)
% 7.56/1.50      | X2 = X3 ),
% 7.56/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_469,plain,
% 7.56/1.50      ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
% 7.56/1.50      | ~ v1_funct_2(X1_52,X0_53,X1_53)
% 7.56/1.50      | ~ v1_funct_2(X0_52,X0_53,X1_53)
% 7.56/1.50      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.56/1.50      | ~ v1_funct_1(X0_52)
% 7.56/1.50      | ~ v1_funct_1(X1_52)
% 7.56/1.50      | X0_52 = X1_52 ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6910,plain,
% 7.56/1.50      ( X0_52 = X1_52
% 7.56/1.50      | r2_funct_2(X0_53,X1_53,X0_52,X1_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 7.56/1.50      | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | v1_funct_1(X1_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11127,plain,
% 7.56/1.50      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_52
% 7.56/1.50      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_11118,c_6910]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10912,plain,
% 7.56/1.50      ( v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_10904,c_6921]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9656,plain,
% 7.56/1.50      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_9650,c_6922]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10591,plain,
% 7.56/1.50      ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_9656,c_37,c_38,c_39,c_40,c_41,c_42,c_46,c_47,c_48,
% 7.56/1.50                 c_49,c_64,c_9085,c_9086]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10592,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK3,X1_51) != iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK3,X0_51,k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_10591]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10913,plain,
% 7.56/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_10904,c_10592]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11456,plain,
% 7.56/1.50      ( v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_52
% 7.56/1.50      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_11127,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_46,c_47,
% 7.56/1.50                 c_48,c_49,c_64,c_9084,c_9085,c_9086,c_10912,c_10913]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11457,plain,
% 7.56/1.50      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = X0_52
% 7.56/1.50      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),X0_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_11456]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11468,plain,
% 7.56/1.50      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_10907,c_11457]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3603,plain,
% 7.56/1.50      ( ~ m1_pre_topc(sK2,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_466]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3604,plain,
% 7.56/1.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK2) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_3603]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_3,plain,
% 7.56/1.50      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_467,plain,
% 7.56/1.50      ( l1_struct_0(X0_51) | ~ l1_pre_topc(X0_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7343,plain,
% 7.56/1.50      ( l1_struct_0(sK1) | ~ l1_pre_topc(sK1) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_467]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7344,plain,
% 7.56/1.50      ( l1_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_7343]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7603,plain,
% 7.56/1.50      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 7.56/1.50      inference(instantiation,[status(thm)],[c_467]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7604,plain,
% 7.56/1.50      ( l1_struct_0(sK2) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_7603]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6913,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7543,plain,
% 7.56/1.50      ( l1_pre_topc(sK3) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6936,c_6913]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7620,plain,
% 7.56/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_7543,c_39,c_46,c_3633]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6912,plain,
% 7.56/1.50      ( l1_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7625,plain,
% 7.56/1.50      ( l1_struct_0(sK3) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_7620,c_6912]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8986,plain,
% 7.56/1.50      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.56/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_8983,c_6920]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8987,plain,
% 7.56/1.50      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.56/1.50      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_8983,c_6921]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8988,plain,
% 7.56/1.50      ( m1_pre_topc(sK0,sK0) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 7.56/1.50      | v2_struct_0(sK0) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK0) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_8983,c_8613]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_8,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.56/1.50      | ~ l1_struct_0(X3)
% 7.56/1.50      | ~ l1_struct_0(X2)
% 7.56/1.50      | ~ l1_struct_0(X1)
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_462,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | m1_subset_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.56/1.50      | ~ l1_struct_0(X2_51)
% 7.56/1.50      | ~ l1_struct_0(X1_51)
% 7.56/1.50      | ~ l1_struct_0(X0_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6917,plain,
% 7.56/1.50      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) = iProver_top
% 7.56/1.50      | l1_struct_0(X2_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X1_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7839,plain,
% 7.56/1.50      ( k2_tmap_1(X0_51,X1_51,X0_52,X2_51) = X1_52
% 7.56/1.50      | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | l1_struct_0(X2_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X1_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | v1_funct_1(X1_52) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6917,c_6910]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_9,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | ~ l1_struct_0(X3)
% 7.56/1.50      | ~ l1_struct_0(X2)
% 7.56/1.50      | ~ l1_struct_0(X1)
% 7.56/1.50      | ~ v1_funct_1(X0) ),
% 7.56/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_461,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | ~ l1_struct_0(X2_51)
% 7.56/1.50      | ~ l1_struct_0(X1_51)
% 7.56/1.50      | ~ l1_struct_0(X0_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_507,plain,
% 7.56/1.50      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | v1_funct_2(k2_tmap_1(X0_51,X1_51,X0_52,X2_51),u1_struct_0(X2_51),u1_struct_0(X1_51)) = iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | l1_struct_0(X2_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X1_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.56/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.56/1.50      | ~ l1_struct_0(X3)
% 7.56/1.50      | ~ l1_struct_0(X2)
% 7.56/1.50      | ~ l1_struct_0(X1)
% 7.56/1.50      | ~ v1_funct_1(X0)
% 7.56/1.50      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_460,plain,
% 7.56/1.50      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | ~ l1_struct_0(X2_51)
% 7.56/1.50      | ~ l1_struct_0(X1_51)
% 7.56/1.50      | ~ l1_struct_0(X0_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52)
% 7.56/1.50      | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_510,plain,
% 7.56/1.50      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | l1_struct_0(X2_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X1_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(X0_51,X1_51,X0_52,X2_51)) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10310,plain,
% 7.56/1.50      ( v1_funct_1(X1_52) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | l1_struct_0(X0_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X1_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X2_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | k2_tmap_1(X0_51,X1_51,X0_52,X2_51) = X1_52
% 7.56/1.50      | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_7839,c_507,c_510]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_10311,plain,
% 7.56/1.50      ( k2_tmap_1(X0_51,X1_51,X0_52,X2_51) = X1_52
% 7.56/1.50      | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) != iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | l1_struct_0(X2_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X1_51) != iProver_top
% 7.56/1.50      | l1_struct_0(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top
% 7.56/1.50      | v1_funct_1(X1_52) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_10310]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11079,plain,
% 7.56/1.50      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | l1_struct_0(sK3) != iProver_top
% 7.56/1.50      | l1_struct_0(sK1) != iProver_top
% 7.56/1.50      | l1_struct_0(sK2) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_10907,c_10311]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11480,plain,
% 7.56/1.50      ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_11468,c_37,c_38,c_39,c_40,c_41,c_42,c_44,c_46,c_47,
% 7.56/1.50                 c_48,c_49,c_64,c_3604,c_7344,c_7604,c_7625,c_8986,
% 7.56/1.50                 c_8987,c_8988,c_9084,c_9085,c_9086,c_11079]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_15,plain,
% 7.56/1.50      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 7.56/1.50      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 7.56/1.50      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.56/1.50      | ~ m1_pre_topc(X4,X0)
% 7.56/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.56/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.56/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.56/1.50      | v2_struct_0(X1)
% 7.56/1.50      | v2_struct_0(X0)
% 7.56/1.50      | v2_struct_0(X4)
% 7.56/1.50      | ~ l1_pre_topc(X1)
% 7.56/1.50      | ~ l1_pre_topc(X0)
% 7.56/1.50      | ~ v2_pre_topc(X1)
% 7.56/1.50      | ~ v2_pre_topc(X0)
% 7.56/1.50      | ~ v1_funct_1(X2) ),
% 7.56/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_455,plain,
% 7.56/1.50      ( ~ r1_tmap_1(X0_51,X1_51,X0_52,X1_52)
% 7.56/1.50      | r1_tmap_1(X2_51,X1_51,k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52)
% 7.56/1.50      | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.56/1.50      | ~ m1_pre_topc(X2_51,X0_51)
% 7.56/1.50      | ~ m1_subset_1(X1_52,u1_struct_0(X2_51))
% 7.56/1.50      | ~ m1_subset_1(X1_52,u1_struct_0(X0_51))
% 7.56/1.50      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.56/1.50      | v2_struct_0(X2_51)
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X0_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51)
% 7.56/1.50      | ~ l1_pre_topc(X0_51)
% 7.56/1.50      | ~ v2_pre_topc(X1_51)
% 7.56/1.50      | ~ v2_pre_topc(X0_51)
% 7.56/1.50      | ~ v1_funct_1(X0_52) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6924,plain,
% 7.56/1.50      ( r1_tmap_1(X0_51,X1_51,X0_52,X1_52) != iProver_top
% 7.56/1.50      | r1_tmap_1(X2_51,X1_51,k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,u1_struct_0(X2_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,u1_struct_0(X0_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X2_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_5,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.56/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.56/1.50      | m1_subset_1(X2,u1_struct_0(X1))
% 7.56/1.50      | v2_struct_0(X1)
% 7.56/1.50      | v2_struct_0(X0)
% 7.56/1.50      | ~ l1_pre_topc(X1) ),
% 7.56/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_465,plain,
% 7.56/1.50      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.56/1.50      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 7.56/1.50      | m1_subset_1(X0_52,u1_struct_0(X1_51))
% 7.56/1.50      | v2_struct_0(X1_51)
% 7.56/1.50      | v2_struct_0(X0_51)
% 7.56/1.50      | ~ l1_pre_topc(X1_51) ),
% 7.56/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_6914,plain,
% 7.56/1.50      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_7238,plain,
% 7.56/1.50      ( r1_tmap_1(X0_51,X1_51,X0_52,X1_52) != iProver_top
% 7.56/1.50      | r1_tmap_1(X2_51,X1_51,k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
% 7.56/1.50      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.56/1.50      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.56/1.50      | m1_subset_1(X1_52,u1_struct_0(X2_51)) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.56/1.50      | v2_struct_0(X2_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X1_51) = iProver_top
% 7.56/1.50      | v2_struct_0(X0_51) = iProver_top
% 7.56/1.50      | l1_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | l1_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X1_51) != iProver_top
% 7.56/1.50      | v2_pre_topc(X0_51) != iProver_top
% 7.56/1.50      | v1_funct_1(X0_52) != iProver_top ),
% 7.56/1.50      inference(forward_subsumption_resolution,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_6924,c_6914]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_11536,plain,
% 7.56/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_52) != iProver_top
% 7.56/1.50      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_52) = iProver_top
% 7.56/1.50      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 7.56/1.50      | m1_pre_topc(sK2,sK3) != iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.56/1.50      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 7.56/1.50      | v2_struct_0(sK3) = iProver_top
% 7.56/1.50      | v2_struct_0(sK1) = iProver_top
% 7.56/1.50      | v2_struct_0(sK2) = iProver_top
% 7.56/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.56/1.50      | l1_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK3) != iProver_top
% 7.56/1.50      | v2_pre_topc(sK1) != iProver_top
% 7.56/1.50      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_11480,c_7238]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_12541,plain,
% 7.56/1.50      ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.56/1.50      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_52) = iProver_top
% 7.56/1.50      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_52) != iProver_top ),
% 7.56/1.50      inference(global_propositional_subsumption,
% 7.56/1.50                [status(thm)],
% 7.56/1.50                [c_11536,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_45,c_46,
% 7.56/1.50                 c_47,c_48,c_49,c_50,c_64,c_3633,c_3635,c_9084,c_9085,
% 7.56/1.50                 c_9086]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_12542,plain,
% 7.56/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0_52) != iProver_top
% 7.56/1.50      | r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X0_52) = iProver_top
% 7.56/1.50      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.56/1.50      inference(renaming,[status(thm)],[c_12541]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_12551,plain,
% 7.56/1.50      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) = iProver_top
% 7.56/1.50      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 7.56/1.50      inference(superposition,[status(thm)],[c_6988,c_12542]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_18,negated_conjecture,
% 7.56/1.50      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
% 7.56/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_54,plain,
% 7.56/1.50      ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) != iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_21,negated_conjecture,
% 7.56/1.50      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.56/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(c_52,plain,
% 7.56/1.50      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.56/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.56/1.50  
% 7.56/1.50  cnf(contradiction,plain,
% 7.56/1.50      ( $false ),
% 7.56/1.50      inference(minisat,[status(thm)],[c_12551,c_54,c_52]) ).
% 7.56/1.50  
% 7.56/1.50  
% 7.56/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.50  
% 7.56/1.50  ------                               Statistics
% 7.56/1.50  
% 7.56/1.50  ------ Selected
% 7.56/1.50  
% 7.56/1.50  total_time:                             0.547
% 7.56/1.50  
%------------------------------------------------------------------------------
