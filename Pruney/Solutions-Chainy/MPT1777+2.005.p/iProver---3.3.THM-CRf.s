%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:25 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3357)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f55,f54,f53,f52,f51,f50,f49])).

fof(f96,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f60,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f70])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f90,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1566,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1623,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1566,c_24])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1560,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1570,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1568,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1698,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1570,c_1568])).

cnf(c_4897,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1698])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1575,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2739,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1575])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1576,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3658,plain,
    ( v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1576])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1578,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1569,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4128,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_1569])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_69,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_92,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5198,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4128,c_69,c_92])).

cnf(c_5199,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5198])).

cnf(c_5207,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_5199])).

cnf(c_5338,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5207,c_43])).

cnf(c_5344,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5338,c_1698])).

cnf(c_5486,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4897,c_42,c_43,c_50,c_2738,c_3357,c_4899])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1562,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4896,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1698])).

cnf(c_1571,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2738,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1575])).

cnf(c_3838,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2738,c_43])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1577,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3843,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
    | v1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3838,c_1577])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1574,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2808,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1574])).

cnf(c_4164,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3843,c_43,c_47,c_2739,c_2808])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_228,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X1)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_7])).

cnf(c_229,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_1552,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(X2,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_2635,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK3
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1552])).

cnf(c_2995,plain,
    ( l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK3
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2635,c_43,c_2739])).

cnf(c_2996,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK3
    | m1_pre_topc(X0,X2) = iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2995])).

cnf(c_3006,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
    | m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_2996])).

cnf(c_4168,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_3006])).

cnf(c_4738,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK3,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4168,c_43,c_2738])).

cnf(c_4739,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4738])).

cnf(c_4748,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_4739])).

cnf(c_4761,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4748,c_43,c_2739])).

cnf(c_4762,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_4761])).

cnf(c_4767,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_4762])).

cnf(c_4869,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4767,c_43,c_2739])).

cnf(c_4898,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4869,c_1698])).

cnf(c_5466,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4896,c_42,c_43,c_2739,c_3658,c_4898])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1579,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5474,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK3)
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5466,c_1579])).

cnf(c_6118,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5486,c_5474])).

cnf(c_3005,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_2996])).

cnf(c_3048,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3005,c_43,c_2739])).

cnf(c_3049,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3048])).

cnf(c_3059,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
    | m1_pre_topc(sK2,X0) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_3049])).

cnf(c_4169,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4164,c_3059])).

cnf(c_4314,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4169,c_43,c_2738])).

cnf(c_4315,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4314])).

cnf(c_4320,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_4315])).

cnf(c_6575,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6118,c_43,c_2739,c_4320,c_4767])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_413,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_1551,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_3844,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3838,c_1551])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_15,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_220,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_15])).

cnf(c_450,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_struct_0(X2) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_220])).

cnf(c_451,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_struct_0(X1) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_20,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_546,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_547,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_551,plain,
    ( ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_30])).

cnf(c_552,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_595,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_552,c_19])).

cnf(c_617,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X0 != X5
    | X3 != X6
    | k2_struct_0(X6) != u1_struct_0(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_451,c_595])).

cnf(c_618,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    | k2_struct_0(X3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_662,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_struct_0(X3) != u1_struct_0(X0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_618,c_7,c_4])).

cnf(c_1550,plain,
    ( k2_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X0,X1,sK4),X4) != iProver_top
    | r1_tmap_1(X0,X2,sK4,X4) = iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_6315,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3844,c_1550])).

cnf(c_6352,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6315])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_49,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11237,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6352,c_49])).

cnf(c_11238,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_11237])).

cnf(c_11260,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11238])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_45,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_46,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14599,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11260,c_44,c_45,c_46,c_53])).

cnf(c_14600,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_14599])).

cnf(c_14616,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6575,c_14600])).

cnf(c_14646,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14616,c_6575])).

cnf(c_14767,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14646,c_43,c_47,c_2739,c_4320])).

cnf(c_14768,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14767])).

cnf(c_14780,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_14768])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_57,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14780,c_57,c_54,c_50,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.98  
% 3.37/0.98  ------  iProver source info
% 3.37/0.98  
% 3.37/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.98  git: non_committed_changes: false
% 3.37/0.98  git: last_make_outside_of_git: false
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     num_symb
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       true
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  ------ Parsing...
% 3.37/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.98  ------ Proving...
% 3.37/0.98  ------ Problem Properties 
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  clauses                                 33
% 3.37/0.98  conjectures                             17
% 3.37/0.98  EPR                                     18
% 3.37/0.98  Horn                                    30
% 3.37/0.98  unary                                   18
% 3.37/0.98  binary                                  2
% 3.37/0.98  lits                                    104
% 3.37/0.98  lits eq                                 13
% 3.37/0.98  fd_pure                                 0
% 3.37/0.98  fd_pseudo                               0
% 3.37/0.98  fd_cond                                 0
% 3.37/0.98  fd_pseudo_cond                          1
% 3.37/0.98  AC symbols                              0
% 3.37/0.98  
% 3.37/0.98  ------ Schedule dynamic 5 is on 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  Current options:
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     none
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       false
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ Proving...
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  % SZS status Theorem for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  fof(f16,conjecture,(
% 3.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f17,negated_conjecture,(
% 3.37/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.37/0.98    inference(negated_conjecture,[],[f16])).
% 3.37/0.98  
% 3.37/0.98  fof(f41,plain,(
% 3.37/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.37/0.98    inference(ennf_transformation,[],[f17])).
% 3.37/0.98  
% 3.37/0.98  fof(f42,plain,(
% 3.37/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.37/0.98    inference(flattening,[],[f41])).
% 3.37/0.98  
% 3.37/0.98  fof(f55,plain,(
% 3.37/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f54,plain,(
% 3.37/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f53,plain,(
% 3.37/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f52,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f51,plain,(
% 3.37/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f50,plain,(
% 3.37/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f49,plain,(
% 3.37/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f56,plain,(
% 3.37/0.98    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.37/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f55,f54,f53,f52,f51,f50,f49])).
% 3.37/0.98  
% 3.37/0.98  fof(f96,plain,(
% 3.37/0.98    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.37/0.98    inference(cnf_transformation,[],[f56])).
% 3.37/0.98  
% 3.37/0.98  fof(f95,plain,(
% 3.37/0.98    sK5 = sK6),
% 3.37/0.98    inference(cnf_transformation,[],[f56])).
% 3.37/0.98  
% 3.37/0.98  fof(f86,plain,(
% 3.37/0.98    m1_pre_topc(sK2,sK0)),
% 3.37/0.98    inference(cnf_transformation,[],[f56])).
% 3.37/0.98  
% 3.37/0.98  fof(f13,axiom,(
% 3.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f35,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/0.98    inference(ennf_transformation,[],[f13])).
% 3.37/0.98  
% 3.37/0.98  fof(f36,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.98    inference(flattening,[],[f35])).
% 3.37/0.98  
% 3.37/0.98  fof(f47,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.98    inference(nnf_transformation,[],[f36])).
% 3.37/0.98  
% 3.37/0.98  fof(f75,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f47])).
% 3.37/0.98  
% 3.37/0.98  fof(f14,axiom,(
% 3.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f37,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/0.98    inference(ennf_transformation,[],[f14])).
% 3.37/0.98  
% 3.37/0.98  fof(f38,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.98    inference(flattening,[],[f37])).
% 3.37/0.98  
% 3.37/0.98  fof(f76,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f38])).
% 3.37/0.98  
% 3.37/0.98  fof(f80,plain,(
% 3.37/0.98    v2_pre_topc(sK0)),
% 3.37/0.98    inference(cnf_transformation,[],[f56])).
% 3.37/0.98  
% 3.37/0.98  fof(f81,plain,(
% 3.37/0.98    l1_pre_topc(sK0)),
% 3.37/0.98    inference(cnf_transformation,[],[f56])).
% 3.37/0.98  
% 3.37/0.98  fof(f6,axiom,(
% 3.37/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f24,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/0.98    inference(ennf_transformation,[],[f6])).
% 3.37/0.98  
% 3.37/0.98  fof(f64,plain,(
% 3.37/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f24])).
% 3.37/0.98  
% 3.37/0.98  fof(f3,axiom,(
% 3.37/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f20,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/0.98    inference(ennf_transformation,[],[f3])).
% 3.37/0.98  
% 3.37/0.98  fof(f21,plain,(
% 3.37/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.98    inference(flattening,[],[f20])).
% 3.37/0.98  
% 3.37/0.98  fof(f61,plain,(
% 3.37/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f21])).
% 3.37/0.98  
% 3.37/0.98  fof(f1,axiom,(
% 3.37/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f43,plain,(
% 3.37/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/0.98    inference(nnf_transformation,[],[f1])).
% 3.37/0.98  
% 3.37/0.98  fof(f44,plain,(
% 3.37/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/0.98    inference(flattening,[],[f43])).
% 3.37/0.98  
% 3.37/0.98  fof(f58,plain,(
% 3.37/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.37/0.98    inference(cnf_transformation,[],[f44])).
% 3.37/0.98  
% 3.37/0.98  fof(f98,plain,(
% 3.37/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.37/0.98    inference(equality_resolution,[],[f58])).
% 3.37/0.98  
% 3.37/0.98  fof(f74,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f47])).
% 3.37/0.98  
% 3.37/0.98  fof(f12,axiom,(
% 3.37/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f34,plain,(
% 3.37/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.37/0.98    inference(ennf_transformation,[],[f12])).
% 3.37/0.99  
% 3.37/0.99  fof(f73,plain,(
% 3.37/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f34])).
% 3.37/0.99  
% 3.37/0.99  fof(f88,plain,(
% 3.37/0.99    m1_pre_topc(sK3,sK0)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f92,plain,(
% 3.37/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f2,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f18,plain,(
% 3.37/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f2])).
% 3.37/0.99  
% 3.37/0.99  fof(f19,plain,(
% 3.37/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f18])).
% 3.37/0.99  
% 3.37/0.99  fof(f60,plain,(
% 3.37/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f19])).
% 3.37/0.99  
% 3.37/0.99  fof(f85,plain,(
% 3.37/0.99    ~v2_struct_0(sK2)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f7,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f25,plain,(
% 3.37/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f7])).
% 3.37/0.99  
% 3.37/0.99  fof(f26,plain,(
% 3.37/0.99    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f25])).
% 3.37/0.99  
% 3.37/0.99  fof(f66,plain,(
% 3.37/0.99    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f26])).
% 3.37/0.99  
% 3.37/0.99  fof(f8,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f27,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f8])).
% 3.37/0.99  
% 3.37/0.99  fof(f28,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f27])).
% 3.37/0.99  
% 3.37/0.99  fof(f67,plain,(
% 3.37/0.99    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f28])).
% 3.37/0.99  
% 3.37/0.99  fof(f59,plain,(
% 3.37/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f44])).
% 3.37/0.99  
% 3.37/0.99  fof(f5,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f23,plain,(
% 3.37/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f5])).
% 3.37/0.99  
% 3.37/0.99  fof(f63,plain,(
% 3.37/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f23])).
% 3.37/0.99  
% 3.37/0.99  fof(f4,axiom,(
% 3.37/0.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f22,plain,(
% 3.37/0.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f4])).
% 3.37/0.99  
% 3.37/0.99  fof(f62,plain,(
% 3.37/0.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f22])).
% 3.37/0.99  
% 3.37/0.99  fof(f9,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f29,plain,(
% 3.37/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f9])).
% 3.37/0.99  
% 3.37/0.99  fof(f30,plain,(
% 3.37/0.99    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f29])).
% 3.37/0.99  
% 3.37/0.99  fof(f68,plain,(
% 3.37/0.99    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f30])).
% 3.37/0.99  
% 3.37/0.99  fof(f10,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f31,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f10])).
% 3.37/0.99  
% 3.37/0.99  fof(f32,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f31])).
% 3.37/0.99  
% 3.37/0.99  fof(f45,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.99    inference(nnf_transformation,[],[f32])).
% 3.37/0.99  
% 3.37/0.99  fof(f46,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.99    inference(flattening,[],[f45])).
% 3.37/0.99  
% 3.37/0.99  fof(f70,plain,(
% 3.37/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f46])).
% 3.37/0.99  
% 3.37/0.99  fof(f101,plain,(
% 3.37/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.99    inference(equality_resolution,[],[f70])).
% 3.37/0.99  
% 3.37/0.99  fof(f11,axiom,(
% 3.37/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f33,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.37/0.99    inference(ennf_transformation,[],[f11])).
% 3.37/0.99  
% 3.37/0.99  fof(f72,plain,(
% 3.37/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f33])).
% 3.37/0.99  
% 3.37/0.99  fof(f15,axiom,(
% 3.37/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.37/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.99  
% 3.37/0.99  fof(f39,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.37/0.99    inference(ennf_transformation,[],[f15])).
% 3.37/0.99  
% 3.37/0.99  fof(f40,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(flattening,[],[f39])).
% 3.37/0.99  
% 3.37/0.99  fof(f48,plain,(
% 3.37/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.37/0.99    inference(nnf_transformation,[],[f40])).
% 3.37/0.99  
% 3.37/0.99  fof(f78,plain,(
% 3.37/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(cnf_transformation,[],[f48])).
% 3.37/0.99  
% 3.37/0.99  fof(f103,plain,(
% 3.37/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.37/0.99    inference(equality_resolution,[],[f78])).
% 3.37/0.99  
% 3.37/0.99  fof(f90,plain,(
% 3.37/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f89,plain,(
% 3.37/0.99    v1_funct_1(sK4)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f87,plain,(
% 3.37/0.99    ~v2_struct_0(sK3)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f82,plain,(
% 3.37/0.99    ~v2_struct_0(sK1)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f83,plain,(
% 3.37/0.99    v2_pre_topc(sK1)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f84,plain,(
% 3.37/0.99    l1_pre_topc(sK1)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f91,plain,(
% 3.37/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f97,plain,(
% 3.37/0.99    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f93,plain,(
% 3.37/0.99    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  fof(f79,plain,(
% 3.37/0.99    ~v2_struct_0(sK0)),
% 3.37/0.99    inference(cnf_transformation,[],[f56])).
% 3.37/0.99  
% 3.37/0.99  cnf(c_23,negated_conjecture,
% 3.37/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.37/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1566,plain,
% 3.37/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_24,negated_conjecture,
% 3.37/0.99      ( sK5 = sK6 ),
% 3.37/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1623,plain,
% 3.37/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_1566,c_24]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_33,negated_conjecture,
% 3.37/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1560,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_17,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ m1_pre_topc(X2,X1)
% 3.37/0.99      | ~ m1_pre_topc(X0,X2)
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1570,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_19,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ m1_pre_topc(X2,X0)
% 3.37/0.99      | m1_pre_topc(X2,X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1568,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.37/0.99      | m1_pre_topc(X2,X1) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1698,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X2),u1_struct_0(X0)) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(forward_subsumption_resolution,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_1570,c_1568]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4897,plain,
% 3.37/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1560,c_1698]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_39,negated_conjecture,
% 3.37/0.99      ( v2_pre_topc(sK0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_42,plain,
% 3.37/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_38,negated_conjecture,
% 3.37/0.99      ( l1_pre_topc(sK0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_43,plain,
% 3.37/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_7,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1575,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2739,plain,
% 3.37/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1560,c_1575]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1576,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | v2_pre_topc(X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3658,plain,
% 3.37/0.99      ( v2_pre_topc(sK0) != iProver_top
% 3.37/0.99      | v2_pre_topc(sK2) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1560,c_1576]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1,plain,
% 3.37/0.99      ( r1_tarski(X0,X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1578,plain,
% 3.37/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_18,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ m1_pre_topc(X2,X1)
% 3.37/0.99      | m1_pre_topc(X0,X2)
% 3.37/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1569,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4128,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X0) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1578,c_1569]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_16,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_69,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_92,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5198,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4128,c_69,c_92]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5199,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_5198]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5207,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK2) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1560,c_5199]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5338,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_5207,c_43]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5344,plain,
% 3.37/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5338,c_1698]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5486,plain,
% 3.37/0.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4897,c_42,c_43,c_50,c_2738,c_3357,c_4899]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_31,negated_conjecture,
% 3.37/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1562,plain,
% 3.37/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4896,plain,
% 3.37/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1562,c_1698]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1571,plain,
% 3.37/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_27,negated_conjecture,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.37/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2738,plain,
% 3.37/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1562,c_1575]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3838,plain,
% 3.37/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2738,c_43]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3,plain,
% 3.37/0.99      ( ~ l1_pre_topc(X0)
% 3.37/0.99      | ~ v1_pre_topc(X0)
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.37/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1577,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | v1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3843,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3
% 3.37/0.99      | v1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_3838,c_1577]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_34,negated_conjecture,
% 3.37/0.99      ( ~ v2_struct_0(sK2) ),
% 3.37/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_47,plain,
% 3.37/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_8,plain,
% 3.37/0.99      ( v2_struct_0(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0)
% 3.37/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1574,plain,
% 3.37/0.99      ( v2_struct_0(X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2808,plain,
% 3.37/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.37/0.99      | v1_pre_topc(sK3) = iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_27,c_1574]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4164,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK3 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_3843,c_43,c_47,c_2739,c_2808]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_10,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | m1_pre_topc(X2,X3)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X3)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X0)
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_228,plain,
% 3.37/0.99      ( ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X3)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | m1_pre_topc(X2,X3)
% 3.37/0.99      | ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_10,c_7]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_229,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | m1_pre_topc(X2,X3)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X3)
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_228]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1552,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
% 3.37/0.99      | m1_pre_topc(X3,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X2,X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2635,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK3
% 3.37/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_27,c_1552]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2995,plain,
% 3.37/0.99      ( l1_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK3
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_2635,c_43,c_2739]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_2996,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != sK3
% 3.37/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_2995]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3006,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
% 3.37/0.99      | m1_pre_topc(X0,X1) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_27,c_2996]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4168,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4164,c_3006]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4738,plain,
% 3.37/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4168,c_43,c_2738]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4739,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) = iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_4738]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4748,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,sK2) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_27,c_4739]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4761,plain,
% 3.37/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4748,c_43,c_2739]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4762,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_4761]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4767,plain,
% 3.37/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1571,c_4762]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4869,plain,
% 3.37/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4767,c_43,c_2739]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4898,plain,
% 3.37/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4869,c_1698]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5466,plain,
% 3.37/0.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4896,c_42,c_43,c_2739,c_3658,c_4898]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_0,plain,
% 3.37/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.37/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1579,plain,
% 3.37/0.99      ( X0 = X1
% 3.37/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.37/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5474,plain,
% 3.37/0.99      ( u1_struct_0(X0) = u1_struct_0(sK3)
% 3.37/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5466,c_1579]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6118,plain,
% 3.37/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK2)
% 3.37/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_5486,c_5474]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3005,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
% 3.37/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,X1) = iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_27,c_2996]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3048,plain,
% 3.37/0.99      ( l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,X1) = iProver_top
% 3.37/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_3005,c_43,c_2739]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3049,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
% 3.37/0.99      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != sK3
% 3.37/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,X1) = iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_3048]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3059,plain,
% 3.37/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
% 3.37/0.99      | m1_pre_topc(sK2,X0) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_27,c_3049]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4169,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_4164,c_3059]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4314,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_4169,c_43,c_2738]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4315,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_4314]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_4320,plain,
% 3.37/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.37/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1571,c_4315]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6575,plain,
% 3.37/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6118,c_43,c_2739,c_4320,c_4767]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6,plain,
% 3.37/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_5,plain,
% 3.37/0.99      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_413,plain,
% 3.37/0.99      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.37/0.99      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1551,plain,
% 3.37/0.99      ( k2_struct_0(X0) = u1_struct_0(X0)
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_3844,plain,
% 3.37/0.99      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_3838,c_1551]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11,plain,
% 3.37/0.99      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.37/0.99      | ~ v2_pre_topc(X0)
% 3.37/0.99      | ~ l1_pre_topc(X0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_13,plain,
% 3.37/0.99      ( v1_tsep_1(X0,X1)
% 3.37/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.37/0.99      | ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_15,plain,
% 3.37/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.37/0.99      | ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_220,plain,
% 3.37/0.99      ( v1_tsep_1(X0,X1)
% 3.37/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.37/0.99      | ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_13,c_15]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_450,plain,
% 3.37/0.99      ( v1_tsep_1(X0,X1)
% 3.37/0.99      | ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | X1 != X2
% 3.37/0.99      | k2_struct_0(X2) != u1_struct_0(X0) ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_220]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_451,plain,
% 3.37/0.99      ( v1_tsep_1(X0,X1)
% 3.37/0.99      | ~ m1_pre_topc(X0,X1)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | k2_struct_0(X1) != u1_struct_0(X0) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_450]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_20,plain,
% 3.37/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.37/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.37/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.37/0.99      | ~ v1_tsep_1(X4,X0)
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.37/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_pre_topc(X4,X5)
% 3.37/0.99      | ~ m1_pre_topc(X0,X5)
% 3.37/0.99      | ~ m1_pre_topc(X4,X0)
% 3.37/0.99      | ~ v1_funct_1(X2)
% 3.37/0.99      | v2_struct_0(X5)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X4)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_pre_topc(X5)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X5)
% 3.37/0.99      | ~ l1_pre_topc(X1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_29,negated_conjecture,
% 3.37/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_546,plain,
% 3.37/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.37/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.37/0.99      | ~ v1_tsep_1(X4,X0)
% 3.37/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.37/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_pre_topc(X4,X5)
% 3.37/0.99      | ~ m1_pre_topc(X0,X5)
% 3.37/0.99      | ~ m1_pre_topc(X4,X0)
% 3.37/0.99      | ~ v1_funct_1(X2)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X5)
% 3.37/0.99      | v2_struct_0(X4)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X5)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X5)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.37/0.99      | sK4 != X2 ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_547,plain,
% 3.37/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ v1_tsep_1(X0,X3)
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_pre_topc(X0,X2)
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | ~ v1_funct_1(sK4)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_546]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_30,negated_conjecture,
% 3.37/0.99      ( v1_funct_1(sK4) ),
% 3.37/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_551,plain,
% 3.37/0.99      ( ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | ~ m1_pre_topc(X0,X2)
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ v1_tsep_1(X0,X3)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_547,c_30]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_552,plain,
% 3.37/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ v1_tsep_1(X0,X3)
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_pre_topc(X0,X2)
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_551]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_595,plain,
% 3.37/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ v1_tsep_1(X0,X3)
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(forward_subsumption_resolution,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_552,c_19]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_617,plain,
% 3.37/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_pre_topc(X5,X6)
% 3.37/0.99      | ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | ~ v2_pre_topc(X6)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X6)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | X0 != X5
% 3.37/0.99      | X3 != X6
% 3.37/0.99      | k2_struct_0(X6) != u1_struct_0(X5)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(resolution_lifted,[status(thm)],[c_451,c_595]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_618,plain,
% 3.37/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ v2_pre_topc(X3)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X3)
% 3.37/0.99      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(unflattening,[status(thm)],[c_617]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_662,plain,
% 3.37/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.37/0.99      | r1_tmap_1(X3,X1,sK4,X4)
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.37/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.37/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.37/0.99      | ~ m1_pre_topc(X3,X2)
% 3.37/0.99      | ~ m1_pre_topc(X0,X3)
% 3.37/0.99      | v2_struct_0(X0)
% 3.37/0.99      | v2_struct_0(X1)
% 3.37/0.99      | v2_struct_0(X3)
% 3.37/0.99      | v2_struct_0(X2)
% 3.37/0.99      | ~ v2_pre_topc(X1)
% 3.37/0.99      | ~ v2_pre_topc(X2)
% 3.37/0.99      | ~ l1_pre_topc(X1)
% 3.37/0.99      | ~ l1_pre_topc(X2)
% 3.37/0.99      | k2_struct_0(X3) != u1_struct_0(X0)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.37/0.99      inference(forward_subsumption_resolution,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_618,c_7,c_4]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_1550,plain,
% 3.37/0.99      ( k2_struct_0(X0) != u1_struct_0(X1)
% 3.37/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X0,X1,sK4),X4) != iProver_top
% 3.37/0.99      | r1_tmap_1(X0,X2,sK4,X4) = iProver_top
% 3.37/0.99      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 3.37/0.99      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 3.37/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,X3) != iProver_top
% 3.37/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.37/0.99      | v2_struct_0(X2) = iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X3) = iProver_top
% 3.37/0.99      | v2_pre_topc(X2) != iProver_top
% 3.37/0.99      | v2_pre_topc(X3) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X3) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6315,plain,
% 3.37/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.37/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X2) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(X2) = iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | v2_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_3844,c_1550]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_6352,plain,
% 3.37/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X2) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X2) = iProver_top
% 3.37/0.99      | v2_struct_0(sK3) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | v2_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.37/0.99      inference(equality_resolution_simp,[status(thm)],[c_6315]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_32,negated_conjecture,
% 3.37/0.99      ( ~ v2_struct_0(sK3) ),
% 3.37/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_49,plain,
% 3.37/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11237,plain,
% 3.37/0.99      ( v2_struct_0(X2) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X2) != iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 3.37/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
% 3.37/0.99      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.37/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | v2_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_6352,c_49]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11238,plain,
% 3.37/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.37/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,X0,sK4,X3) = iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.37/0.99      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 3.37/0.99      | m1_pre_topc(X1,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X2) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X2) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | v2_pre_topc(X2) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_11237]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_11260,plain,
% 3.37/0.99      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.37/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.37/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X1) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(sK1) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.37/0.99      inference(equality_resolution,[status(thm)],[c_11238]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_37,negated_conjecture,
% 3.37/0.99      ( ~ v2_struct_0(sK1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_44,plain,
% 3.37/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_36,negated_conjecture,
% 3.37/0.99      ( v2_pre_topc(sK1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_45,plain,
% 3.37/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_35,negated_conjecture,
% 3.37/0.99      ( l1_pre_topc(sK1) ),
% 3.37/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_46,plain,
% 3.37/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_28,negated_conjecture,
% 3.37/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.37/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_53,plain,
% 3.37/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14599,plain,
% 3.37/0.99      ( l1_pre_topc(X1) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X1) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.37/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.37/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_11260,c_44,c_45,c_46,c_53]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14600,plain,
% 3.37/0.99      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.37/0.99      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.37/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.37/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_pre_topc(X0,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X1) != iProver_top
% 3.37/0.99      | v2_struct_0(X1) = iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_pre_topc(X1) != iProver_top
% 3.37/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_14599]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14616,plain,
% 3.37/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.37/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.37/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(sK2) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_6575,c_14600]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14646,plain,
% 3.37/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.37/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_struct_0(sK2) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(light_normalisation,[status(thm)],[c_14616,c_6575]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14767,plain,
% 3.37/0.99      ( v2_struct_0(X0) = iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.37/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(global_propositional_subsumption,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_14646,c_43,c_47,c_2739,c_4320]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14768,plain,
% 3.37/0.99      ( r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),X1) != iProver_top
% 3.37/0.99      | r1_tmap_1(sK3,sK1,sK4,X1) = iProver_top
% 3.37/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,X0) != iProver_top
% 3.37/0.99      | v2_struct_0(X0) = iProver_top
% 3.37/0.99      | v2_pre_topc(X0) != iProver_top
% 3.37/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.37/0.99      inference(renaming,[status(thm)],[c_14767]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_14780,plain,
% 3.37/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.37/0.99      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.37/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.37/0.99      | v2_struct_0(sK0) = iProver_top
% 3.37/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.37/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.37/0.99      inference(superposition,[status(thm)],[c_1623,c_14768]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_22,negated_conjecture,
% 3.37/0.99      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.37/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_57,plain,
% 3.37/0.99      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_26,negated_conjecture,
% 3.37/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.37/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_54,plain,
% 3.37/0.99      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_50,plain,
% 3.37/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_40,negated_conjecture,
% 3.37/0.99      ( ~ v2_struct_0(sK0) ),
% 3.37/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(c_41,plain,
% 3.37/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.37/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.37/0.99  
% 3.37/0.99  cnf(contradiction,plain,
% 3.37/0.99      ( $false ),
% 3.37/0.99      inference(minisat,
% 3.37/0.99                [status(thm)],
% 3.37/0.99                [c_14780,c_57,c_54,c_50,c_43,c_42,c_41]) ).
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.99  
% 3.37/0.99  ------                               Statistics
% 3.37/0.99  
% 3.37/0.99  ------ General
% 3.37/0.99  
% 3.37/0.99  abstr_ref_over_cycles:                  0
% 3.37/0.99  abstr_ref_under_cycles:                 0
% 3.37/0.99  gc_basic_clause_elim:                   0
% 3.37/0.99  forced_gc_time:                         0
% 3.37/0.99  parsing_time:                           0.01
% 3.37/0.99  unif_index_cands_time:                  0.
% 3.37/0.99  unif_index_add_time:                    0.
% 3.37/0.99  orderings_time:                         0.
% 3.37/0.99  out_proof_time:                         0.012
% 3.37/0.99  total_time:                             0.438
% 3.37/0.99  num_of_symbols:                         58
% 3.37/0.99  num_of_terms:                           5941
% 3.37/0.99  
% 3.37/0.99  ------ Preprocessing
% 3.37/0.99  
% 3.37/0.99  num_of_splits:                          0
% 3.37/0.99  num_of_split_atoms:                     0
% 3.37/0.99  num_of_reused_defs:                     0
% 3.37/0.99  num_eq_ax_congr_red:                    7
% 3.37/0.99  num_of_sem_filtered_clauses:            1
% 3.37/0.99  num_of_subtypes:                        0
% 3.37/0.99  monotx_restored_types:                  0
% 3.37/0.99  sat_num_of_epr_types:                   0
% 3.37/0.99  sat_num_of_non_cyclic_types:            0
% 3.37/0.99  sat_guarded_non_collapsed_types:        0
% 3.37/0.99  num_pure_diseq_elim:                    0
% 3.37/0.99  simp_replaced_by:                       0
% 3.37/0.99  res_preprocessed:                       171
% 3.37/0.99  prep_upred:                             0
% 3.37/0.99  prep_unflattend:                        9
% 3.37/0.99  smt_new_axioms:                         0
% 3.37/0.99  pred_elim_cands:                        8
% 3.37/0.99  pred_elim:                              5
% 3.37/0.99  pred_elim_cl:                           6
% 3.37/0.99  pred_elim_cycles:                       8
% 3.37/0.99  merged_defs:                            0
% 3.37/0.99  merged_defs_ncl:                        0
% 3.37/0.99  bin_hyper_res:                          0
% 3.37/0.99  prep_cycles:                            4
% 3.37/0.99  pred_elim_time:                         0.014
% 3.37/0.99  splitting_time:                         0.
% 3.37/0.99  sem_filter_time:                        0.
% 3.37/0.99  monotx_time:                            0.
% 3.37/0.99  subtype_inf_time:                       0.
% 3.37/0.99  
% 3.37/0.99  ------ Problem properties
% 3.37/0.99  
% 3.37/0.99  clauses:                                33
% 3.37/0.99  conjectures:                            17
% 3.37/0.99  epr:                                    18
% 3.37/0.99  horn:                                   30
% 3.37/0.99  ground:                                 17
% 3.37/0.99  unary:                                  18
% 3.37/0.99  binary:                                 2
% 3.37/0.99  lits:                                   104
% 3.37/0.99  lits_eq:                                13
% 3.37/0.99  fd_pure:                                0
% 3.37/0.99  fd_pseudo:                              0
% 3.37/0.99  fd_cond:                                0
% 3.37/0.99  fd_pseudo_cond:                         1
% 3.37/0.99  ac_symbols:                             0
% 3.37/0.99  
% 3.37/0.99  ------ Propositional Solver
% 3.37/0.99  
% 3.37/0.99  prop_solver_calls:                      30
% 3.37/0.99  prop_fast_solver_calls:                 3125
% 3.37/0.99  smt_solver_calls:                       0
% 3.37/0.99  smt_fast_solver_calls:                  0
% 3.37/0.99  prop_num_of_clauses:                    4237
% 3.37/0.99  prop_preprocess_simplified:             9527
% 3.37/0.99  prop_fo_subsumed:                       181
% 3.37/0.99  prop_solver_time:                       0.
% 3.37/0.99  smt_solver_time:                        0.
% 3.37/0.99  smt_fast_solver_time:                   0.
% 3.37/0.99  prop_fast_solver_time:                  0.
% 3.37/0.99  prop_unsat_core_time:                   0.
% 3.37/0.99  
% 3.37/0.99  ------ QBF
% 3.37/0.99  
% 3.37/0.99  qbf_q_res:                              0
% 3.37/0.99  qbf_num_tautologies:                    0
% 3.37/0.99  qbf_prep_cycles:                        0
% 3.37/0.99  
% 3.37/0.99  ------ BMC1
% 3.37/0.99  
% 3.37/0.99  bmc1_current_bound:                     -1
% 3.37/0.99  bmc1_last_solved_bound:                 -1
% 3.37/0.99  bmc1_unsat_core_size:                   -1
% 3.37/0.99  bmc1_unsat_core_parents_size:           -1
% 3.37/0.99  bmc1_merge_next_fun:                    0
% 3.37/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.37/0.99  
% 3.37/0.99  ------ Instantiation
% 3.37/0.99  
% 3.37/0.99  inst_num_of_clauses:                    1283
% 3.37/0.99  inst_num_in_passive:                    61
% 3.37/0.99  inst_num_in_active:                     761
% 3.37/0.99  inst_num_in_unprocessed:                461
% 3.37/0.99  inst_num_of_loops:                      790
% 3.37/0.99  inst_num_of_learning_restarts:          0
% 3.37/0.99  inst_num_moves_active_passive:          25
% 3.37/0.99  inst_lit_activity:                      0
% 3.37/0.99  inst_lit_activity_moves:                0
% 3.37/0.99  inst_num_tautologies:                   0
% 3.37/0.99  inst_num_prop_implied:                  0
% 3.37/0.99  inst_num_existing_simplified:           0
% 3.37/0.99  inst_num_eq_res_simplified:             0
% 3.37/0.99  inst_num_child_elim:                    0
% 3.37/0.99  inst_num_of_dismatching_blockings:      844
% 3.37/0.99  inst_num_of_non_proper_insts:           2360
% 3.37/0.99  inst_num_of_duplicates:                 0
% 3.37/0.99  inst_inst_num_from_inst_to_res:         0
% 3.37/0.99  inst_dismatching_checking_time:         0.
% 3.37/0.99  
% 3.37/0.99  ------ Resolution
% 3.37/0.99  
% 3.37/0.99  res_num_of_clauses:                     0
% 3.37/0.99  res_num_in_passive:                     0
% 3.37/0.99  res_num_in_active:                      0
% 3.37/0.99  res_num_of_loops:                       175
% 3.37/0.99  res_forward_subset_subsumed:            312
% 3.37/0.99  res_backward_subset_subsumed:           4
% 3.37/0.99  res_forward_subsumed:                   0
% 3.37/0.99  res_backward_subsumed:                  0
% 3.37/0.99  res_forward_subsumption_resolution:     6
% 3.37/0.99  res_backward_subsumption_resolution:    0
% 3.37/0.99  res_clause_to_clause_subsumption:       1888
% 3.37/0.99  res_orphan_elimination:                 0
% 3.37/0.99  res_tautology_del:                      424
% 3.37/0.99  res_num_eq_res_simplified:              0
% 3.37/0.99  res_num_sel_changes:                    0
% 3.37/0.99  res_moves_from_active_to_pass:          0
% 3.37/0.99  
% 3.37/0.99  ------ Superposition
% 3.37/0.99  
% 3.37/0.99  sup_time_total:                         0.
% 3.37/0.99  sup_time_generating:                    0.
% 3.37/0.99  sup_time_sim_full:                      0.
% 3.37/0.99  sup_time_sim_immed:                     0.
% 3.37/0.99  
% 3.37/0.99  sup_num_of_clauses:                     159
% 3.37/0.99  sup_num_in_active:                      153
% 3.37/0.99  sup_num_in_passive:                     6
% 3.37/0.99  sup_num_of_loops:                       157
% 3.37/0.99  sup_fw_superposition:                   191
% 3.37/0.99  sup_bw_superposition:                   96
% 3.37/0.99  sup_immediate_simplified:               100
% 3.37/0.99  sup_given_eliminated:                   0
% 3.37/0.99  comparisons_done:                       0
% 3.37/0.99  comparisons_avoided:                    0
% 3.37/0.99  
% 3.37/0.99  ------ Simplifications
% 3.37/0.99  
% 3.37/0.99  
% 3.37/0.99  sim_fw_subset_subsumed:                 53
% 3.37/0.99  sim_bw_subset_subsumed:                 9
% 3.37/0.99  sim_fw_subsumed:                        21
% 3.37/0.99  sim_bw_subsumed:                        1
% 3.37/0.99  sim_fw_subsumption_res:                 3
% 3.37/0.99  sim_bw_subsumption_res:                 0
% 3.37/0.99  sim_tautology_del:                      31
% 3.37/0.99  sim_eq_tautology_del:                   18
% 3.37/0.99  sim_eq_res_simp:                        4
% 3.37/0.99  sim_fw_demodulated:                     2
% 3.37/0.99  sim_bw_demodulated:                     5
% 3.37/0.99  sim_light_normalised:                   39
% 3.37/0.99  sim_joinable_taut:                      0
% 3.37/0.99  sim_joinable_simp:                      0
% 3.37/0.99  sim_ac_normalised:                      0
% 3.37/0.99  sim_smt_subsumption:                    0
% 3.37/0.99  
%------------------------------------------------------------------------------
