%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:34 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2670)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f49,f48,f47,f46,f45,f44,f43])).

fof(f88,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    sK5 = sK6 ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f70])).

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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9887,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_494,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1508,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | X0 != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_5707,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v3_pre_topc(k2_struct_0(X1),X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_8519,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5707])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1120,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1188,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1120,c_22])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1123,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X5) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1124,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1348,plain,
    ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_tsep_1(X4,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X4,X0) != iProver_top
    | m1_pre_topc(X0,X5) != iProver_top
    | v2_struct_0(X5) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X5) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X5) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1123,c_1124])).

cnf(c_7651,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1348])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1110,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1132,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2231,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1132])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1133,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2455,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2231,c_1133])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1114,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1131,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2342,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1131])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1800,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

cnf(c_1801,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_2543,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2342,c_41,c_1801])).

cnf(c_2548,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_1132])).

cnf(c_2654,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2548,c_1133])).

cnf(c_7669,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7651,c_2455,c_2654])).

cnf(c_7687,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7669])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1112,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1126,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1285,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1126,c_1124])).

cnf(c_5408,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_1285])).

cnf(c_2343,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_1131])).

cnf(c_1802,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

cnf(c_1803,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_2551,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2343,c_41,c_1803])).

cnf(c_2556,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_1132])).

cnf(c_2657,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2556,c_1133])).

cnf(c_5443,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5408,c_2657])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5804,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5443,c_40,c_41,c_1801,c_2670,c_5425])).

cnf(c_5813,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_5804])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1127,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1130,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4424,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2657,c_1130])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3989,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_2657,c_25])).

cnf(c_4456,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4424,c_3989])).

cnf(c_5078,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4456,c_41,c_1803])).

cnf(c_5079,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5078])).

cnf(c_5087,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_5079])).

cnf(c_6061,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5813,c_41,c_1801,c_5087])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1136,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6066,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6061,c_1136])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_269,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_6])).

cnf(c_270,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_269])).

cnf(c_1104,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_2980,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1104])).

cnf(c_3150,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2980,c_41,c_1803])).

cnf(c_3151,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3150])).

cnf(c_3158,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_3151])).

cnf(c_5407,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1114,c_1285])).

cnf(c_5452,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5407,c_2654])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2671,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_31])).

cnf(c_2672,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2671])).

cnf(c_5197,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5087,c_41,c_1801])).

cnf(c_5411,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5197,c_1285])).

cnf(c_5416,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5411,c_2654])).

cnf(c_6021,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5452,c_40,c_41,c_1803,c_2672,c_5416])).

cnf(c_6029,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2657,c_6021])).

cnf(c_6828,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6066,c_41,c_1803,c_3158,c_6029])).

cnf(c_6838,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_6828,c_2657])).

cnf(c_11,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_13,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_282,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_13])).

cnf(c_4353,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1118,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3599,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2654,c_1118])).

cnf(c_3608,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3599])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1116,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2793,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2455,c_1116])).

cnf(c_3598,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2654,c_2793])).

cnf(c_3607,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3598])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1117,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2792,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2455,c_1117])).

cnf(c_3597,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2654,c_2792])).

cnf(c_3606,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3597])).

cnf(c_3159,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3158])).

cnf(c_2669,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_29])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1119,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1165,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1119,c_22])).

cnf(c_1386,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1165])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9887,c_8519,c_7687,c_6838,c_4353,c_3608,c_3607,c_3606,c_3159,c_2669,c_1802,c_1800,c_1386,c_20,c_28,c_29,c_30,c_32,c_33,c_34,c_35,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.77/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/1.00  
% 3.77/1.00  ------  iProver source info
% 3.77/1.00  
% 3.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/1.00  git: non_committed_changes: false
% 3.77/1.00  git: last_make_outside_of_git: false
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  ------ Parsing...
% 3.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/1.00  ------ Proving...
% 3.77/1.00  ------ Problem Properties 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  clauses                                 37
% 3.77/1.00  conjectures                             19
% 3.77/1.00  EPR                                     20
% 3.77/1.00  Horn                                    35
% 3.77/1.00  unary                                   20
% 3.77/1.00  binary                                  3
% 3.77/1.00  lits                                    114
% 3.77/1.00  lits eq                                 4
% 3.77/1.00  fd_pure                                 0
% 3.77/1.00  fd_pseudo                               0
% 3.77/1.00  fd_cond                                 0
% 3.77/1.00  fd_pseudo_cond                          1
% 3.77/1.00  AC symbols                              0
% 3.77/1.00  
% 3.77/1.00  ------ Input Options Time Limit: Unbounded
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  Current options:
% 3.77/1.00  ------ 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ Proving...
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS status Theorem for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  fof(f7,axiom,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f22,plain,(
% 3.77/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f7])).
% 3.77/1.00  
% 3.77/1.00  fof(f23,plain,(
% 3.77/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f60,plain,(
% 3.77/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f23])).
% 3.77/1.00  
% 3.77/1.00  fof(f14,conjecture,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f15,negated_conjecture,(
% 3.77/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.77/1.00    inference(negated_conjecture,[],[f14])).
% 3.77/1.00  
% 3.77/1.00  fof(f34,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f15])).
% 3.77/1.00  
% 3.77/1.00  fof(f35,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.77/1.00    inference(flattening,[],[f34])).
% 3.77/1.00  
% 3.77/1.00  fof(f49,plain,(
% 3.77/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f48,plain,(
% 3.77/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f47,plain,(
% 3.77/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f46,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f45,plain,(
% 3.77/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f44,plain,(
% 3.77/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f43,plain,(
% 3.77/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f50,plain,(
% 3.77/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f49,f48,f47,f46,f45,f44,f43])).
% 3.77/1.00  
% 3.77/1.00  fof(f88,plain,(
% 3.77/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f87,plain,(
% 3.77/1.00    sK5 = sK6),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f13,axiom,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f32,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f13])).
% 3.77/1.00  
% 3.77/1.00  fof(f33,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.77/1.00    inference(flattening,[],[f32])).
% 3.77/1.00  
% 3.77/1.00  fof(f42,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.77/1.00    inference(nnf_transformation,[],[f33])).
% 3.77/1.00  
% 3.77/1.00  fof(f70,plain,(
% 3.77/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f42])).
% 3.77/1.00  
% 3.77/1.00  fof(f95,plain,(
% 3.77/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.77/1.00    inference(equality_resolution,[],[f70])).
% 3.77/1.00  
% 3.77/1.00  fof(f12,axiom,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f30,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f12])).
% 3.77/1.00  
% 3.77/1.00  fof(f31,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f30])).
% 3.77/1.00  
% 3.77/1.00  fof(f68,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f31])).
% 3.77/1.00  
% 3.77/1.00  fof(f76,plain,(
% 3.77/1.00    l1_pre_topc(sK1)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f4,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f19,plain,(
% 3.77/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f4])).
% 3.77/1.00  
% 3.77/1.00  fof(f56,plain,(
% 3.77/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f19])).
% 3.77/1.00  
% 3.77/1.00  fof(f3,axiom,(
% 3.77/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f18,plain,(
% 3.77/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f3])).
% 3.77/1.00  
% 3.77/1.00  fof(f55,plain,(
% 3.77/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f18])).
% 3.77/1.00  
% 3.77/1.00  fof(f80,plain,(
% 3.77/1.00    m1_pre_topc(sK3,sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f5,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f20,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f5])).
% 3.77/1.00  
% 3.77/1.00  fof(f57,plain,(
% 3.77/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f20])).
% 3.77/1.00  
% 3.77/1.00  fof(f73,plain,(
% 3.77/1.00    l1_pre_topc(sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f78,plain,(
% 3.77/1.00    m1_pre_topc(sK2,sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f11,axiom,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f28,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f11])).
% 3.77/1.00  
% 3.77/1.00  fof(f29,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f28])).
% 3.77/1.00  
% 3.77/1.00  fof(f41,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(nnf_transformation,[],[f29])).
% 3.77/1.00  
% 3.77/1.00  fof(f67,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f41])).
% 3.77/1.00  
% 3.77/1.00  fof(f72,plain,(
% 3.77/1.00    v2_pre_topc(sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f10,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f27,plain,(
% 3.77/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f10])).
% 3.77/1.00  
% 3.77/1.00  fof(f65,plain,(
% 3.77/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f6,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f21,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f6])).
% 3.77/1.00  
% 3.77/1.00  fof(f38,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(nnf_transformation,[],[f21])).
% 3.77/1.00  
% 3.77/1.00  fof(f59,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f38])).
% 3.77/1.00  
% 3.77/1.00  fof(f84,plain,(
% 3.77/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f1,axiom,(
% 3.77/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f36,plain,(
% 3.77/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/1.00    inference(nnf_transformation,[],[f1])).
% 3.77/1.00  
% 3.77/1.00  fof(f37,plain,(
% 3.77/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/1.00    inference(flattening,[],[f36])).
% 3.77/1.00  
% 3.77/1.00  fof(f53,plain,(
% 3.77/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f37])).
% 3.77/1.00  
% 3.77/1.00  fof(f58,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f38])).
% 3.77/1.00  
% 3.77/1.00  fof(f2,axiom,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f16,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f2])).
% 3.77/1.00  
% 3.77/1.00  fof(f17,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f16])).
% 3.77/1.00  
% 3.77/1.00  fof(f54,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f17])).
% 3.77/1.00  
% 3.77/1.00  fof(f8,axiom,(
% 3.77/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f24,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f8])).
% 3.77/1.00  
% 3.77/1.00  fof(f25,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f24])).
% 3.77/1.00  
% 3.77/1.00  fof(f39,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(nnf_transformation,[],[f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f40,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.77/1.00    inference(flattening,[],[f39])).
% 3.77/1.00  
% 3.77/1.00  fof(f62,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f40])).
% 3.77/1.00  
% 3.77/1.00  fof(f93,plain,(
% 3.77/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.77/1.00    inference(equality_resolution,[],[f62])).
% 3.77/1.00  
% 3.77/1.00  fof(f9,axiom,(
% 3.77/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f26,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f9])).
% 3.77/1.00  
% 3.77/1.00  fof(f64,plain,(
% 3.77/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f85,plain,(
% 3.77/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f82,plain,(
% 3.77/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f83,plain,(
% 3.77/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f86,plain,(
% 3.77/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f89,plain,(
% 3.77/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f81,plain,(
% 3.77/1.00    v1_funct_1(sK4)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f79,plain,(
% 3.77/1.00    ~v2_struct_0(sK3)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f77,plain,(
% 3.77/1.00    ~v2_struct_0(sK2)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f75,plain,(
% 3.77/1.00    v2_pre_topc(sK1)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f74,plain,(
% 3.77/1.00    ~v2_struct_0(sK1)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  fof(f71,plain,(
% 3.77/1.00    ~v2_struct_0(sK0)),
% 3.77/1.00    inference(cnf_transformation,[],[f50])).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9,plain,
% 3.77/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.77/1.00      | ~ l1_pre_topc(X0)
% 3.77/1.00      | ~ v2_pre_topc(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9887,plain,
% 3.77/1.00      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.77/1.00      | ~ l1_pre_topc(sK3)
% 3.77/1.00      | ~ v2_pre_topc(sK3) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_494,plain,
% 3.77/1.00      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 3.77/1.00      theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1508,plain,
% 3.77/1.00      ( v3_pre_topc(X0,X1)
% 3.77/1.00      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.77/1.00      | X0 != k2_struct_0(X1) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_494]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5707,plain,
% 3.77/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.77/1.00      | ~ v3_pre_topc(k2_struct_0(X1),X1)
% 3.77/1.00      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1508]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8519,plain,
% 3.77/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.77/1.00      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 3.77/1.00      | u1_struct_0(sK2) != k2_struct_0(sK3) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_5707]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_21,negated_conjecture,
% 3.77/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1120,plain,
% 3.77/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_22,negated_conjecture,
% 3.77/1.00      ( sK5 = sK6 ),
% 3.77/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1188,plain,
% 3.77/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_1120,c_22]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_18,plain,
% 3.77/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.77/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.77/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.77/1.00      | ~ v1_tsep_1(X4,X0)
% 3.77/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.77/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.77/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.77/1.00      | ~ m1_pre_topc(X4,X5)
% 3.77/1.00      | ~ m1_pre_topc(X4,X0)
% 3.77/1.00      | ~ m1_pre_topc(X0,X5)
% 3.77/1.00      | v2_struct_0(X5)
% 3.77/1.00      | v2_struct_0(X1)
% 3.77/1.00      | v2_struct_0(X4)
% 3.77/1.00      | v2_struct_0(X0)
% 3.77/1.00      | ~ v1_funct_1(X2)
% 3.77/1.00      | ~ l1_pre_topc(X5)
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X5)
% 3.77/1.00      | ~ v2_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1123,plain,
% 3.77/1.00      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.77/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.77/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.77/1.00      | v1_tsep_1(X4,X0) != iProver_top
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.77/1.00      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.77/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.77/1.00      | m1_pre_topc(X4,X5) != iProver_top
% 3.77/1.00      | m1_pre_topc(X4,X0) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,X5) != iProver_top
% 3.77/1.00      | v2_struct_0(X5) = iProver_top
% 3.77/1.00      | v2_struct_0(X1) = iProver_top
% 3.77/1.00      | v2_struct_0(X4) = iProver_top
% 3.77/1.00      | v2_struct_0(X0) = iProver_top
% 3.77/1.00      | v1_funct_1(X2) != iProver_top
% 3.77/1.00      | l1_pre_topc(X5) != iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | v2_pre_topc(X5) != iProver_top
% 3.77/1.00      | v2_pre_topc(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_17,plain,
% 3.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_pre_topc(X2,X0)
% 3.77/1.00      | m1_pre_topc(X2,X1)
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1124,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.77/1.00      | m1_pre_topc(X2,X1) = iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | v2_pre_topc(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1348,plain,
% 3.77/1.00      ( r1_tmap_1(X0,X1,X2,X3) = iProver_top
% 3.77/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3) != iProver_top
% 3.77/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.77/1.00      | v1_tsep_1(X4,X0) != iProver_top
% 3.77/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.77/1.00      | m1_subset_1(X3,u1_struct_0(X4)) != iProver_top
% 3.77/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.77/1.00      | m1_pre_topc(X4,X0) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,X5) != iProver_top
% 3.77/1.00      | v2_struct_0(X5) = iProver_top
% 3.77/1.00      | v2_struct_0(X1) = iProver_top
% 3.77/1.00      | v2_struct_0(X4) = iProver_top
% 3.77/1.00      | v2_struct_0(X0) = iProver_top
% 3.77/1.00      | v1_funct_1(X2) != iProver_top
% 3.77/1.00      | l1_pre_topc(X5) != iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | v2_pre_topc(X5) != iProver_top
% 3.77/1.00      | v2_pre_topc(X1) != iProver_top ),
% 3.77/1.00      inference(forward_subsumption_resolution,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_1123,c_1124]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7651,plain,
% 3.77/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.77/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.77/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.77/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.77/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.77/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.77/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.77/1.00      | v2_struct_0(sK0) = iProver_top
% 3.77/1.00      | v2_struct_0(sK2) = iProver_top
% 3.77/1.00      | v2_struct_0(sK1) = iProver_top
% 3.77/1.00      | v2_struct_0(sK3) = iProver_top
% 3.77/1.00      | v1_funct_1(sK4) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1188,c_1348]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_33,negated_conjecture,
% 3.77/1.00      ( l1_pre_topc(sK1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1110,plain,
% 3.77/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5,plain,
% 3.77/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1132,plain,
% 3.77/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2231,plain,
% 3.77/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1110,c_1132]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4,plain,
% 3.77/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1133,plain,
% 3.77/1.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.77/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2455,plain,
% 3.77/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2231,c_1133]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_29,negated_conjecture,
% 3.77/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1114,plain,
% 3.77/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6,plain,
% 3.77/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1131,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2342,plain,
% 3.77/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1114,c_1131]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_36,negated_conjecture,
% 3.77/1.00      ( l1_pre_topc(sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_41,plain,
% 3.77/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1800,plain,
% 3.77/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_6,c_29]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1801,plain,
% 3.77/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2543,plain,
% 3.77/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_2342,c_41,c_1801]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2548,plain,
% 3.77/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2543,c_1132]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2654,plain,
% 3.77/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2548,c_1133]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7669,plain,
% 3.77/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.77/1.00      | v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top
% 3.77/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.77/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.77/1.00      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 3.77/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) != iProver_top
% 3.77/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.77/1.00      | v2_struct_0(sK0) = iProver_top
% 3.77/1.00      | v2_struct_0(sK2) = iProver_top
% 3.77/1.00      | v2_struct_0(sK1) = iProver_top
% 3.77/1.00      | v2_struct_0(sK3) = iProver_top
% 3.77/1.00      | v1_funct_1(sK4) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_7651,c_2455,c_2654]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7687,plain,
% 3.77/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5)
% 3.77/1.00      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
% 3.77/1.00      | ~ v1_tsep_1(sK2,sK3)
% 3.77/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 3.77/1.00      | ~ m1_subset_1(sK5,k2_struct_0(sK3))
% 3.77/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
% 3.77/1.00      | ~ m1_pre_topc(sK2,sK3)
% 3.77/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.77/1.00      | v2_struct_0(sK0)
% 3.77/1.00      | v2_struct_0(sK2)
% 3.77/1.00      | v2_struct_0(sK1)
% 3.77/1.00      | v2_struct_0(sK3)
% 3.77/1.00      | ~ v1_funct_1(sK4)
% 3.77/1.00      | ~ l1_pre_topc(sK0)
% 3.77/1.00      | ~ l1_pre_topc(sK1)
% 3.77/1.00      | ~ v2_pre_topc(sK0)
% 3.77/1.00      | ~ v2_pre_topc(sK1) ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7669]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_31,negated_conjecture,
% 3.77/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1112,plain,
% 3.77/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_15,plain,
% 3.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_pre_topc(X0,X2)
% 3.77/1.00      | ~ m1_pre_topc(X2,X1)
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1126,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | v2_pre_topc(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1285,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | v2_pre_topc(X1) != iProver_top ),
% 3.77/1.00      inference(forward_subsumption_resolution,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_1126,c_1124]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5408,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1112,c_1285]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2343,plain,
% 3.77/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1112,c_1131]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1802,plain,
% 3.77/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_6,c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1803,plain,
% 3.77/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2551,plain,
% 3.77/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_2343,c_41,c_1803]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2556,plain,
% 3.77/1.00      ( l1_struct_0(sK2) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2551,c_1132]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2657,plain,
% 3.77/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2556,c_1133]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5443,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_5408,c_2657]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_37,negated_conjecture,
% 3.77/1.00      ( v2_pre_topc(sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_40,plain,
% 3.77/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5804,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_5443,c_40,c_41,c_1801,c_2670,c_5425]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5813,plain,
% 3.77/1.00      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.77/1.00      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2654,c_5804]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_14,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1127,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 3.77/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X0)
% 3.77/1.00      | ~ l1_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1130,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1) = iProver_top
% 3.77/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top
% 3.77/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4424,plain,
% 3.77/1.00      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK2) = iProver_top
% 3.77/1.00      | l1_pre_topc(X0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2657,c_1130]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_25,negated_conjecture,
% 3.77/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.77/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3989,plain,
% 3.77/1.00      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2657,c_25]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4456,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | l1_pre_topc(X0) != iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_4424,c_3989]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5078,plain,
% 3.77/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK2) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_4456,c_41,c_1803]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5079,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) = iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_5078]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5087,plain,
% 3.77/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1127,c_5079]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6061,plain,
% 3.77/1.00      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_5813,c_41,c_1801,c_5087]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_0,plain,
% 3.77/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.77/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1136,plain,
% 3.77/1.00      ( X0 = X1
% 3.77/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.77/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6066,plain,
% 3.77/1.00      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.77/1.00      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_6061,c_1136]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8,plain,
% 3.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X0)
% 3.77/1.00      | ~ l1_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_269,plain,
% 3.77/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.77/1.00      | ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ l1_pre_topc(X1) ),
% 3.77/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8,c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_270,plain,
% 3.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.77/1.00      | ~ l1_pre_topc(X1) ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_269]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1104,plain,
% 3.77/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.77/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2980,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK3) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_25,c_1104]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3150,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK3) = iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_2980,c_41,c_1803]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3151,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.77/1.00      | m1_pre_topc(X0,sK3) = iProver_top ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_3150]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3158,plain,
% 3.77/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1127,c_3151]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5407,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1114,c_1285]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5452,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_5407,c_2654]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3,plain,
% 3.77/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X1)
% 3.77/1.00      | v2_pre_topc(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2671,plain,
% 3.77/1.00      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_3,c_31]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2672,plain,
% 3.77/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK2) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_2671]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5197,plain,
% 3.77/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_5087,c_41,c_1801]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5411,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_5197,c_1285]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5416,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 3.77/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.77/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_5411,c_2654]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6021,plain,
% 3.77/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.77/1.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_5452,c_40,c_41,c_1803,c_2672,c_5416]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6029,plain,
% 3.77/1.00      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.77/1.00      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_2657,c_6021]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6828,plain,
% 3.77/1.00      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_6066,c_41,c_1803,c_3158,c_6029]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6838,plain,
% 3.77/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_6828,c_2657]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11,plain,
% 3.77/1.00      ( v1_tsep_1(X0,X1)
% 3.77/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.77/1.00      | ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13,plain,
% 3.77/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.77/1.00      | ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ l1_pre_topc(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_282,plain,
% 3.77/1.00      ( v1_tsep_1(X0,X1)
% 3.77/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.77/1.00      | ~ m1_pre_topc(X0,X1)
% 3.77/1.00      | ~ l1_pre_topc(X1)
% 3.77/1.00      | ~ v2_pre_topc(X1) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_11,c_13]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_4353,plain,
% 3.77/1.00      ( v1_tsep_1(sK2,sK3)
% 3.77/1.00      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 3.77/1.00      | ~ m1_pre_topc(sK2,sK3)
% 3.77/1.00      | ~ l1_pre_topc(sK3)
% 3.77/1.00      | ~ v2_pre_topc(sK3) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_282]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_24,negated_conjecture,
% 3.77/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1118,plain,
% 3.77/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3599,plain,
% 3.77/1.00      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2654,c_1118]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3608,plain,
% 3.77/1.00      ( m1_subset_1(sK5,k2_struct_0(sK3)) ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3599]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_27,negated_conjecture,
% 3.77/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1116,plain,
% 3.77/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2793,plain,
% 3.77/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2455,c_1116]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3598,plain,
% 3.77/1.00      ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2654,c_2793]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3607,plain,
% 3.77/1.00      ( v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3598]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_26,negated_conjecture,
% 3.77/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.77/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1117,plain,
% 3.77/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2792,plain,
% 3.77/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2455,c_1117]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3597,plain,
% 3.77/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 3.77/1.00      inference(demodulation,[status(thm)],[c_2654,c_2792]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3606,plain,
% 3.77/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3597]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3159,plain,
% 3.77/1.00      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3158]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2669,plain,
% 3.77/1.00      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 3.77/1.00      inference(resolution,[status(thm)],[c_3,c_29]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_23,negated_conjecture,
% 3.77/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1119,plain,
% 3.77/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1165,plain,
% 3.77/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_1119,c_22]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1386,plain,
% 3.77/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1165]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_20,negated_conjecture,
% 3.77/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.77/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_28,negated_conjecture,
% 3.77/1.00      ( v1_funct_1(sK4) ),
% 3.77/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_30,negated_conjecture,
% 3.77/1.00      ( ~ v2_struct_0(sK3) ),
% 3.77/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_32,negated_conjecture,
% 3.77/1.00      ( ~ v2_struct_0(sK2) ),
% 3.77/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_34,negated_conjecture,
% 3.77/1.00      ( v2_pre_topc(sK1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_35,negated_conjecture,
% 3.77/1.00      ( ~ v2_struct_0(sK1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_38,negated_conjecture,
% 3.77/1.00      ( ~ v2_struct_0(sK0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(contradiction,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(minisat,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_9887,c_8519,c_7687,c_6838,c_4353,c_3608,c_3607,c_3606,
% 3.77/1.00                 c_3159,c_2669,c_1802,c_1800,c_1386,c_20,c_28,c_29,c_30,
% 3.77/1.00                 c_32,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ Selected
% 3.77/1.00  
% 3.77/1.00  total_time:                             0.309
% 3.77/1.00  
%------------------------------------------------------------------------------
