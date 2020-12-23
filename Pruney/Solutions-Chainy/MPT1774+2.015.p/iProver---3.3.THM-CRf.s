%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:15 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2225)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | ~ r1_tmap_1(X3,X0,X4,X6) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
            | r1_tmap_1(X3,X0,X4,X6) )
          & X6 = X7
          & r1_tarski(X5,u1_struct_0(X2))
          & r2_hidden(X6,X5)
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X7,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK8 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | ~ r1_tmap_1(X3,X0,X4,X6) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                | r1_tmap_1(X3,X0,X4,X6) )
              & X6 = X7
              & r1_tarski(X5,u1_struct_0(X2))
              & r2_hidden(X6,X5)
              & v3_pre_topc(X5,X1)
              & m1_subset_1(X7,u1_struct_0(X2)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | ~ r1_tmap_1(X3,X0,X4,sK7) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK7) )
            & sK7 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK7,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                    | r1_tmap_1(X3,X0,X4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(X2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,X1)
                  & m1_subset_1(X7,u1_struct_0(X2)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                  | r1_tmap_1(X3,X0,X4,X6) )
                & X6 = X7
                & r1_tarski(sK6,u1_struct_0(X2))
                & r2_hidden(X6,sK6)
                & v3_pre_topc(sK6,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X0,X4,X6) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                        | r1_tmap_1(X3,X0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(X2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,X1)
                      & m1_subset_1(X7,u1_struct_0(X2)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X0,sK5,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7)
                      | r1_tmap_1(X3,X0,sK5,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X0,X4,X6) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                            | r1_tmap_1(X3,X0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(X2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,X1)
                          & m1_subset_1(X7,u1_struct_0(X2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | ~ r1_tmap_1(sK4,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7)
                          | r1_tmap_1(sK4,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X0,X4,X6) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,X0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,X1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK3))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK3)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK2)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK1,X4,X6) )
                                  & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK1,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK7) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
      | r1_tmap_1(sK4,sK1,sK5,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK3))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK2)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).

fof(f80,plain,(
    r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f44])).

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
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f58])).

fof(f72,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f57])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f56])).

fof(f83,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
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

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( X3 = X4
                          & r1_tarski(X3,X2)
                          & r1_tarski(X2,u1_struct_0(X1))
                          & v3_pre_topc(X2,X0) )
                       => ( v3_pre_topc(X4,X1)
                        <=> v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( v3_pre_topc(X4,X1)
                          | ~ v3_pre_topc(X3,X0) )
                        & ( v3_pre_topc(X3,X0)
                          | ~ v3_pre_topc(X4,X1) ) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v3_pre_topc(X4,X1)
      | ~ v3_pre_topc(X3,X0)
      | X3 != X4
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(X4,X1)
      | ~ v3_pre_topc(X4,X0)
      | ~ r1_tarski(X4,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f79,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1889,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1898,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_17,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK7)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1890,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1974,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1890,c_18])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_547,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_548,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_552,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v3_pre_topc(X5,X3)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_548,c_28])).

cnf(c_553,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_602,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_553,c_10])).

cnf(c_1870,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
    | v3_pre_topc(X5,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(X4,X5) != iProver_top
    | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2379,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1870])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_47,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_984,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2222,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_2223,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
    | r1_tmap_1(sK4,X1,sK5,X3)
    | ~ v3_pre_topc(X4,sK4)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_2229,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2223])).

cnf(c_3266,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_47,c_2222,c_2229])).

cnf(c_3267,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
    | v3_pre_topc(X4,sK4) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X3,X4) != iProver_top
    | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3266])).

cnf(c_3291,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
    | v3_pre_topc(X3,sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3267])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6057,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
    | v3_pre_topc(X3,sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_39,c_40,c_41,c_51])).

cnf(c_6058,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
    | v3_pre_topc(X3,sK4) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6057])).

cnf(c_6077,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1974,c_6058])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_48,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_52,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_55,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1885,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1935,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1885,c_18])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_195,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_481,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_27])).

cnf(c_482,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_28])).

cnf(c_487,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_486])).

cnf(c_528,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_487,c_10])).

cnf(c_1871,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_2883,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1871])).

cnf(c_3218,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2883,c_47,c_2222,c_2225])).

cnf(c_3219,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
    | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
    | m1_pre_topc(X1,sK4) != iProver_top
    | m1_pre_topc(sK4,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3218])).

cnf(c_3239,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3219])).

cnf(c_3296,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3239,c_39,c_40,c_41,c_51])).

cnf(c_3297,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
    | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3296])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1891,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1979,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1891,c_18])).

cnf(c_3312,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3297,c_1979])).

cnf(c_6396,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6077,c_42,c_43,c_44,c_45,c_48,c_52,c_55,c_1935,c_3312])).

cnf(c_6406,plain,
    ( v3_pre_topc(X0,sK4) != iProver_top
    | r2_hidden(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_6396])).

cnf(c_6670,plain,
    ( v3_pre_topc(sK6,sK4) != iProver_top
    | r2_hidden(sK8,sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_6406])).

cnf(c_1881,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1896,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1894,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2012,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1896,c_1894])).

cnf(c_5440,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1881,c_2012])).

cnf(c_5840,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5440,c_43,c_44])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1902,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1901,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3752,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1902,c_1901])).

cnf(c_5480,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_1901])).

cnf(c_6232,plain,
    ( r2_hidden(sK0(sK6,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X1) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_5480])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1903,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6377,plain,
    ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6232,c_1903])).

cnf(c_6471,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5840,c_6377])).

cnf(c_4746,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4747,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4746])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(X2,u1_struct_0(X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2347,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v3_pre_topc(sK6,X1)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(sK6,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2616,plain,
    ( v3_pre_topc(sK6,X0)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6,u1_struct_0(X0))
    | ~ r1_tarski(sK6,sK6)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_3314,plain,
    ( v3_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6,u1_struct_0(sK4))
    | ~ r1_tarski(sK6,sK6)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_3315,plain,
    ( v3_pre_topc(sK6,sK4) = iProver_top
    | v3_pre_topc(sK6,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK6,sK6) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3314])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2950,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2951,plain,
    ( r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2950])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1888,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1930,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1888,c_18])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_56,plain,
    ( v3_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_53,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6670,c_6471,c_4747,c_3315,c_2951,c_1930,c_56,c_53,c_52,c_48,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:31:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.64/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/0.97  
% 2.64/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/0.97  
% 2.64/0.97  ------  iProver source info
% 2.64/0.97  
% 2.64/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.64/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/0.97  git: non_committed_changes: false
% 2.64/0.97  git: last_make_outside_of_git: false
% 2.64/0.97  
% 2.64/0.97  ------ 
% 2.64/0.97  
% 2.64/0.97  ------ Input Options
% 2.64/0.97  
% 2.64/0.97  --out_options                           all
% 2.64/0.97  --tptp_safe_out                         true
% 2.64/0.97  --problem_path                          ""
% 2.64/0.97  --include_path                          ""
% 2.64/0.97  --clausifier                            res/vclausify_rel
% 2.64/0.97  --clausifier_options                    --mode clausify
% 2.64/0.97  --stdin                                 false
% 2.64/0.97  --stats_out                             all
% 2.64/0.97  
% 2.64/0.97  ------ General Options
% 2.64/0.97  
% 2.64/0.97  --fof                                   false
% 2.64/0.97  --time_out_real                         305.
% 2.64/0.97  --time_out_virtual                      -1.
% 2.64/0.97  --symbol_type_check                     false
% 2.64/0.97  --clausify_out                          false
% 2.64/0.97  --sig_cnt_out                           false
% 2.64/0.97  --trig_cnt_out                          false
% 2.64/0.97  --trig_cnt_out_tolerance                1.
% 2.64/0.97  --trig_cnt_out_sk_spl                   false
% 2.64/0.97  --abstr_cl_out                          false
% 2.64/0.97  
% 2.64/0.97  ------ Global Options
% 2.64/0.97  
% 2.64/0.97  --schedule                              default
% 2.64/0.97  --add_important_lit                     false
% 2.64/0.97  --prop_solver_per_cl                    1000
% 2.64/0.97  --min_unsat_core                        false
% 2.64/0.97  --soft_assumptions                      false
% 2.64/0.97  --soft_lemma_size                       3
% 2.64/0.97  --prop_impl_unit_size                   0
% 2.64/0.97  --prop_impl_unit                        []
% 2.64/0.97  --share_sel_clauses                     true
% 2.64/0.97  --reset_solvers                         false
% 2.64/0.97  --bc_imp_inh                            [conj_cone]
% 2.64/0.97  --conj_cone_tolerance                   3.
% 2.64/0.97  --extra_neg_conj                        none
% 2.64/0.97  --large_theory_mode                     true
% 2.64/0.97  --prolific_symb_bound                   200
% 2.64/0.97  --lt_threshold                          2000
% 2.64/0.97  --clause_weak_htbl                      true
% 2.64/0.97  --gc_record_bc_elim                     false
% 2.64/0.97  
% 2.64/0.97  ------ Preprocessing Options
% 2.64/0.97  
% 2.64/0.97  --preprocessing_flag                    true
% 2.64/0.97  --time_out_prep_mult                    0.1
% 2.64/0.97  --splitting_mode                        input
% 2.64/0.97  --splitting_grd                         true
% 2.64/0.97  --splitting_cvd                         false
% 2.64/0.97  --splitting_cvd_svl                     false
% 2.64/0.97  --splitting_nvd                         32
% 2.64/0.97  --sub_typing                            true
% 2.64/0.97  --prep_gs_sim                           true
% 2.64/0.97  --prep_unflatten                        true
% 2.64/0.97  --prep_res_sim                          true
% 2.64/0.97  --prep_upred                            true
% 2.64/0.97  --prep_sem_filter                       exhaustive
% 2.64/0.97  --prep_sem_filter_out                   false
% 2.64/0.97  --pred_elim                             true
% 2.64/0.97  --res_sim_input                         true
% 2.64/0.97  --eq_ax_congr_red                       true
% 2.64/0.97  --pure_diseq_elim                       true
% 2.64/0.97  --brand_transform                       false
% 2.64/0.97  --non_eq_to_eq                          false
% 2.64/0.97  --prep_def_merge                        true
% 2.64/0.97  --prep_def_merge_prop_impl              false
% 2.64/0.97  --prep_def_merge_mbd                    true
% 2.64/0.97  --prep_def_merge_tr_red                 false
% 2.64/0.97  --prep_def_merge_tr_cl                  false
% 2.64/0.97  --smt_preprocessing                     true
% 2.64/0.97  --smt_ac_axioms                         fast
% 2.64/0.97  --preprocessed_out                      false
% 2.64/0.97  --preprocessed_stats                    false
% 2.64/0.97  
% 2.64/0.97  ------ Abstraction refinement Options
% 2.64/0.97  
% 2.64/0.97  --abstr_ref                             []
% 2.64/0.97  --abstr_ref_prep                        false
% 2.64/0.97  --abstr_ref_until_sat                   false
% 2.64/0.97  --abstr_ref_sig_restrict                funpre
% 2.64/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.97  --abstr_ref_under                       []
% 2.64/0.97  
% 2.64/0.97  ------ SAT Options
% 2.64/0.97  
% 2.64/0.97  --sat_mode                              false
% 2.64/0.97  --sat_fm_restart_options                ""
% 2.64/0.97  --sat_gr_def                            false
% 2.64/0.97  --sat_epr_types                         true
% 2.64/0.97  --sat_non_cyclic_types                  false
% 2.64/0.97  --sat_finite_models                     false
% 2.64/0.97  --sat_fm_lemmas                         false
% 2.64/0.97  --sat_fm_prep                           false
% 2.64/0.97  --sat_fm_uc_incr                        true
% 2.64/0.97  --sat_out_model                         small
% 2.64/0.97  --sat_out_clauses                       false
% 2.64/0.97  
% 2.64/0.97  ------ QBF Options
% 2.64/0.97  
% 2.64/0.97  --qbf_mode                              false
% 2.64/0.97  --qbf_elim_univ                         false
% 2.64/0.97  --qbf_dom_inst                          none
% 2.64/0.97  --qbf_dom_pre_inst                      false
% 2.64/0.97  --qbf_sk_in                             false
% 2.64/0.97  --qbf_pred_elim                         true
% 2.64/0.97  --qbf_split                             512
% 2.64/0.97  
% 2.64/0.97  ------ BMC1 Options
% 2.64/0.97  
% 2.64/0.97  --bmc1_incremental                      false
% 2.64/0.97  --bmc1_axioms                           reachable_all
% 2.64/0.97  --bmc1_min_bound                        0
% 2.64/0.97  --bmc1_max_bound                        -1
% 2.64/0.97  --bmc1_max_bound_default                -1
% 2.64/0.97  --bmc1_symbol_reachability              true
% 2.64/0.97  --bmc1_property_lemmas                  false
% 2.64/0.97  --bmc1_k_induction                      false
% 2.64/0.97  --bmc1_non_equiv_states                 false
% 2.64/0.97  --bmc1_deadlock                         false
% 2.64/0.97  --bmc1_ucm                              false
% 2.64/0.97  --bmc1_add_unsat_core                   none
% 2.64/0.97  --bmc1_unsat_core_children              false
% 2.64/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.97  --bmc1_out_stat                         full
% 2.64/0.97  --bmc1_ground_init                      false
% 2.64/0.97  --bmc1_pre_inst_next_state              false
% 2.64/0.97  --bmc1_pre_inst_state                   false
% 2.64/0.97  --bmc1_pre_inst_reach_state             false
% 2.64/0.97  --bmc1_out_unsat_core                   false
% 2.64/0.97  --bmc1_aig_witness_out                  false
% 2.64/0.97  --bmc1_verbose                          false
% 2.64/0.97  --bmc1_dump_clauses_tptp                false
% 2.64/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.97  --bmc1_dump_file                        -
% 2.64/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.97  --bmc1_ucm_extend_mode                  1
% 2.64/0.97  --bmc1_ucm_init_mode                    2
% 2.64/0.97  --bmc1_ucm_cone_mode                    none
% 2.64/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.97  --bmc1_ucm_relax_model                  4
% 2.64/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.97  --bmc1_ucm_layered_model                none
% 2.64/0.97  --bmc1_ucm_max_lemma_size               10
% 2.64/0.97  
% 2.64/0.97  ------ AIG Options
% 2.64/0.97  
% 2.64/0.97  --aig_mode                              false
% 2.64/0.97  
% 2.64/0.97  ------ Instantiation Options
% 2.64/0.97  
% 2.64/0.97  --instantiation_flag                    true
% 2.64/0.97  --inst_sos_flag                         false
% 2.64/0.97  --inst_sos_phase                        true
% 2.64/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.97  --inst_lit_sel_side                     num_symb
% 2.64/0.97  --inst_solver_per_active                1400
% 2.64/0.97  --inst_solver_calls_frac                1.
% 2.64/0.97  --inst_passive_queue_type               priority_queues
% 2.64/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.97  --inst_passive_queues_freq              [25;2]
% 2.64/0.97  --inst_dismatching                      true
% 2.64/0.97  --inst_eager_unprocessed_to_passive     true
% 2.64/0.97  --inst_prop_sim_given                   true
% 2.64/0.97  --inst_prop_sim_new                     false
% 2.64/0.97  --inst_subs_new                         false
% 2.64/0.97  --inst_eq_res_simp                      false
% 2.64/0.97  --inst_subs_given                       false
% 2.64/0.97  --inst_orphan_elimination               true
% 2.64/0.97  --inst_learning_loop_flag               true
% 2.64/0.97  --inst_learning_start                   3000
% 2.64/0.97  --inst_learning_factor                  2
% 2.64/0.97  --inst_start_prop_sim_after_learn       3
% 2.64/0.97  --inst_sel_renew                        solver
% 2.64/0.97  --inst_lit_activity_flag                true
% 2.64/0.97  --inst_restr_to_given                   false
% 2.64/0.97  --inst_activity_threshold               500
% 2.64/0.97  --inst_out_proof                        true
% 2.64/0.97  
% 2.64/0.97  ------ Resolution Options
% 2.64/0.97  
% 2.64/0.97  --resolution_flag                       true
% 2.64/0.97  --res_lit_sel                           adaptive
% 2.64/0.97  --res_lit_sel_side                      none
% 2.64/0.97  --res_ordering                          kbo
% 2.64/0.97  --res_to_prop_solver                    active
% 2.64/0.97  --res_prop_simpl_new                    false
% 2.64/0.97  --res_prop_simpl_given                  true
% 2.64/0.97  --res_passive_queue_type                priority_queues
% 2.64/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.97  --res_passive_queues_freq               [15;5]
% 2.64/0.97  --res_forward_subs                      full
% 2.64/0.97  --res_backward_subs                     full
% 2.64/0.97  --res_forward_subs_resolution           true
% 2.64/0.97  --res_backward_subs_resolution          true
% 2.64/0.97  --res_orphan_elimination                true
% 2.64/0.97  --res_time_limit                        2.
% 2.64/0.97  --res_out_proof                         true
% 2.64/0.97  
% 2.64/0.97  ------ Superposition Options
% 2.64/0.97  
% 2.64/0.97  --superposition_flag                    true
% 2.64/0.97  --sup_passive_queue_type                priority_queues
% 2.64/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.97  --demod_completeness_check              fast
% 2.64/0.97  --demod_use_ground                      true
% 2.64/0.97  --sup_to_prop_solver                    passive
% 2.64/0.97  --sup_prop_simpl_new                    true
% 2.64/0.97  --sup_prop_simpl_given                  true
% 2.64/0.97  --sup_fun_splitting                     false
% 2.64/0.97  --sup_smt_interval                      50000
% 2.64/0.97  
% 2.64/0.97  ------ Superposition Simplification Setup
% 2.64/0.97  
% 2.64/0.97  --sup_indices_passive                   []
% 2.64/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.97  --sup_full_bw                           [BwDemod]
% 2.64/0.97  --sup_immed_triv                        [TrivRules]
% 2.64/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.97  --sup_immed_bw_main                     []
% 2.64/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.97  
% 2.64/0.97  ------ Combination Options
% 2.64/0.97  
% 2.64/0.97  --comb_res_mult                         3
% 2.64/0.97  --comb_sup_mult                         2
% 2.64/0.97  --comb_inst_mult                        10
% 2.64/0.97  
% 2.64/0.97  ------ Debug Options
% 2.64/0.97  
% 2.64/0.97  --dbg_backtrace                         false
% 2.64/0.97  --dbg_dump_prop_clauses                 false
% 2.64/0.97  --dbg_dump_prop_clauses_file            -
% 2.64/0.97  --dbg_out_stat                          false
% 2.64/0.97  ------ Parsing...
% 2.64/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/0.97  
% 2.64/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.64/0.97  
% 2.64/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/0.97  
% 2.64/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/0.97  ------ Proving...
% 2.64/0.97  ------ Problem Properties 
% 2.64/0.97  
% 2.64/0.97  
% 2.64/0.97  clauses                                 35
% 2.64/0.97  conjectures                             21
% 2.64/0.97  EPR                                     18
% 2.64/0.97  Horn                                    31
% 2.64/0.97  unary                                   20
% 2.64/0.97  binary                                  6
% 2.64/0.97  lits                                    115
% 2.64/0.97  lits eq                                 6
% 2.64/0.97  fd_pure                                 0
% 2.64/0.97  fd_pseudo                               0
% 2.64/0.97  fd_cond                                 0
% 2.64/0.97  fd_pseudo_cond                          1
% 2.64/0.97  AC symbols                              0
% 2.64/0.97  
% 2.64/0.97  ------ Schedule dynamic 5 is on 
% 2.64/0.97  
% 2.64/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/0.97  
% 2.64/0.97  
% 2.64/0.97  ------ 
% 2.64/0.97  Current options:
% 2.64/0.97  ------ 
% 2.64/0.97  
% 2.64/0.97  ------ Input Options
% 2.64/0.97  
% 2.64/0.97  --out_options                           all
% 2.64/0.97  --tptp_safe_out                         true
% 2.64/0.97  --problem_path                          ""
% 2.64/0.97  --include_path                          ""
% 2.64/0.97  --clausifier                            res/vclausify_rel
% 2.64/0.97  --clausifier_options                    --mode clausify
% 2.64/0.97  --stdin                                 false
% 2.64/0.97  --stats_out                             all
% 2.64/0.97  
% 2.64/0.97  ------ General Options
% 2.64/0.97  
% 2.64/0.97  --fof                                   false
% 2.64/0.97  --time_out_real                         305.
% 2.64/0.97  --time_out_virtual                      -1.
% 2.64/0.97  --symbol_type_check                     false
% 2.64/0.97  --clausify_out                          false
% 2.64/0.97  --sig_cnt_out                           false
% 2.64/0.97  --trig_cnt_out                          false
% 2.64/0.97  --trig_cnt_out_tolerance                1.
% 2.64/0.97  --trig_cnt_out_sk_spl                   false
% 2.64/0.97  --abstr_cl_out                          false
% 2.64/0.97  
% 2.64/0.97  ------ Global Options
% 2.64/0.97  
% 2.64/0.97  --schedule                              default
% 2.64/0.97  --add_important_lit                     false
% 2.64/0.97  --prop_solver_per_cl                    1000
% 2.64/0.97  --min_unsat_core                        false
% 2.64/0.97  --soft_assumptions                      false
% 2.64/0.97  --soft_lemma_size                       3
% 2.64/0.97  --prop_impl_unit_size                   0
% 2.64/0.97  --prop_impl_unit                        []
% 2.64/0.97  --share_sel_clauses                     true
% 2.64/0.97  --reset_solvers                         false
% 2.64/0.97  --bc_imp_inh                            [conj_cone]
% 2.64/0.97  --conj_cone_tolerance                   3.
% 2.64/0.97  --extra_neg_conj                        none
% 2.64/0.97  --large_theory_mode                     true
% 2.64/0.97  --prolific_symb_bound                   200
% 2.64/0.97  --lt_threshold                          2000
% 2.64/0.97  --clause_weak_htbl                      true
% 2.64/0.97  --gc_record_bc_elim                     false
% 2.64/0.97  
% 2.64/0.97  ------ Preprocessing Options
% 2.64/0.97  
% 2.64/0.97  --preprocessing_flag                    true
% 2.64/0.97  --time_out_prep_mult                    0.1
% 2.64/0.97  --splitting_mode                        input
% 2.64/0.97  --splitting_grd                         true
% 2.64/0.97  --splitting_cvd                         false
% 2.64/0.97  --splitting_cvd_svl                     false
% 2.64/0.97  --splitting_nvd                         32
% 2.64/0.97  --sub_typing                            true
% 2.64/0.97  --prep_gs_sim                           true
% 2.64/0.97  --prep_unflatten                        true
% 2.64/0.97  --prep_res_sim                          true
% 2.64/0.97  --prep_upred                            true
% 2.64/0.97  --prep_sem_filter                       exhaustive
% 2.64/0.97  --prep_sem_filter_out                   false
% 2.64/0.97  --pred_elim                             true
% 2.64/0.97  --res_sim_input                         true
% 2.64/0.97  --eq_ax_congr_red                       true
% 2.64/0.97  --pure_diseq_elim                       true
% 2.64/0.97  --brand_transform                       false
% 2.64/0.97  --non_eq_to_eq                          false
% 2.64/0.97  --prep_def_merge                        true
% 2.64/0.97  --prep_def_merge_prop_impl              false
% 2.64/0.97  --prep_def_merge_mbd                    true
% 2.64/0.97  --prep_def_merge_tr_red                 false
% 2.64/0.97  --prep_def_merge_tr_cl                  false
% 2.64/0.97  --smt_preprocessing                     true
% 2.64/0.97  --smt_ac_axioms                         fast
% 2.64/0.97  --preprocessed_out                      false
% 2.64/0.97  --preprocessed_stats                    false
% 2.64/0.97  
% 2.64/0.97  ------ Abstraction refinement Options
% 2.64/0.97  
% 2.64/0.97  --abstr_ref                             []
% 2.64/0.97  --abstr_ref_prep                        false
% 2.64/0.97  --abstr_ref_until_sat                   false
% 2.64/0.97  --abstr_ref_sig_restrict                funpre
% 2.64/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.97  --abstr_ref_under                       []
% 2.64/0.97  
% 2.64/0.97  ------ SAT Options
% 2.64/0.97  
% 2.64/0.97  --sat_mode                              false
% 2.64/0.97  --sat_fm_restart_options                ""
% 2.64/0.97  --sat_gr_def                            false
% 2.64/0.97  --sat_epr_types                         true
% 2.64/0.97  --sat_non_cyclic_types                  false
% 2.64/0.97  --sat_finite_models                     false
% 2.64/0.97  --sat_fm_lemmas                         false
% 2.64/0.97  --sat_fm_prep                           false
% 2.64/0.97  --sat_fm_uc_incr                        true
% 2.64/0.97  --sat_out_model                         small
% 2.64/0.97  --sat_out_clauses                       false
% 2.64/0.97  
% 2.64/0.97  ------ QBF Options
% 2.64/0.97  
% 2.64/0.97  --qbf_mode                              false
% 2.64/0.97  --qbf_elim_univ                         false
% 2.64/0.97  --qbf_dom_inst                          none
% 2.64/0.97  --qbf_dom_pre_inst                      false
% 2.64/0.97  --qbf_sk_in                             false
% 2.64/0.97  --qbf_pred_elim                         true
% 2.64/0.97  --qbf_split                             512
% 2.64/0.97  
% 2.64/0.97  ------ BMC1 Options
% 2.64/0.97  
% 2.64/0.97  --bmc1_incremental                      false
% 2.64/0.97  --bmc1_axioms                           reachable_all
% 2.64/0.97  --bmc1_min_bound                        0
% 2.64/0.97  --bmc1_max_bound                        -1
% 2.64/0.97  --bmc1_max_bound_default                -1
% 2.64/0.97  --bmc1_symbol_reachability              true
% 2.64/0.97  --bmc1_property_lemmas                  false
% 2.64/0.97  --bmc1_k_induction                      false
% 2.64/0.97  --bmc1_non_equiv_states                 false
% 2.64/0.97  --bmc1_deadlock                         false
% 2.64/0.97  --bmc1_ucm                              false
% 2.64/0.97  --bmc1_add_unsat_core                   none
% 2.64/0.97  --bmc1_unsat_core_children              false
% 2.64/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.97  --bmc1_out_stat                         full
% 2.64/0.97  --bmc1_ground_init                      false
% 2.64/0.97  --bmc1_pre_inst_next_state              false
% 2.64/0.97  --bmc1_pre_inst_state                   false
% 2.64/0.97  --bmc1_pre_inst_reach_state             false
% 2.64/0.97  --bmc1_out_unsat_core                   false
% 2.64/0.97  --bmc1_aig_witness_out                  false
% 2.64/0.97  --bmc1_verbose                          false
% 2.64/0.97  --bmc1_dump_clauses_tptp                false
% 2.64/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.97  --bmc1_dump_file                        -
% 2.64/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.97  --bmc1_ucm_extend_mode                  1
% 2.64/0.97  --bmc1_ucm_init_mode                    2
% 2.64/0.97  --bmc1_ucm_cone_mode                    none
% 2.64/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.97  --bmc1_ucm_relax_model                  4
% 2.64/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.97  --bmc1_ucm_layered_model                none
% 2.64/0.97  --bmc1_ucm_max_lemma_size               10
% 2.64/0.97  
% 2.64/0.97  ------ AIG Options
% 2.64/0.97  
% 2.64/0.97  --aig_mode                              false
% 2.64/0.97  
% 2.64/0.97  ------ Instantiation Options
% 2.64/0.97  
% 2.64/0.97  --instantiation_flag                    true
% 2.64/0.97  --inst_sos_flag                         false
% 2.64/0.97  --inst_sos_phase                        true
% 2.64/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.97  --inst_lit_sel_side                     none
% 2.64/0.97  --inst_solver_per_active                1400
% 2.64/0.97  --inst_solver_calls_frac                1.
% 2.64/0.97  --inst_passive_queue_type               priority_queues
% 2.64/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.97  --inst_passive_queues_freq              [25;2]
% 2.64/0.97  --inst_dismatching                      true
% 2.64/0.97  --inst_eager_unprocessed_to_passive     true
% 2.64/0.97  --inst_prop_sim_given                   true
% 2.64/0.97  --inst_prop_sim_new                     false
% 2.64/0.97  --inst_subs_new                         false
% 2.64/0.97  --inst_eq_res_simp                      false
% 2.64/0.97  --inst_subs_given                       false
% 2.64/0.97  --inst_orphan_elimination               true
% 2.64/0.97  --inst_learning_loop_flag               true
% 2.64/0.97  --inst_learning_start                   3000
% 2.64/0.97  --inst_learning_factor                  2
% 2.64/0.97  --inst_start_prop_sim_after_learn       3
% 2.64/0.97  --inst_sel_renew                        solver
% 2.64/0.97  --inst_lit_activity_flag                true
% 2.64/0.97  --inst_restr_to_given                   false
% 2.64/0.97  --inst_activity_threshold               500
% 2.64/0.97  --inst_out_proof                        true
% 2.64/0.97  
% 2.64/0.97  ------ Resolution Options
% 2.64/0.97  
% 2.64/0.97  --resolution_flag                       false
% 2.64/0.97  --res_lit_sel                           adaptive
% 2.64/0.97  --res_lit_sel_side                      none
% 2.64/0.97  --res_ordering                          kbo
% 2.64/0.97  --res_to_prop_solver                    active
% 2.64/0.97  --res_prop_simpl_new                    false
% 2.64/0.97  --res_prop_simpl_given                  true
% 2.64/0.97  --res_passive_queue_type                priority_queues
% 2.64/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.97  --res_passive_queues_freq               [15;5]
% 2.64/0.97  --res_forward_subs                      full
% 2.64/0.97  --res_backward_subs                     full
% 2.64/0.97  --res_forward_subs_resolution           true
% 2.64/0.97  --res_backward_subs_resolution          true
% 2.64/0.97  --res_orphan_elimination                true
% 2.64/0.97  --res_time_limit                        2.
% 2.64/0.97  --res_out_proof                         true
% 2.64/0.97  
% 2.64/0.97  ------ Superposition Options
% 2.64/0.97  
% 2.64/0.97  --superposition_flag                    true
% 2.64/0.97  --sup_passive_queue_type                priority_queues
% 2.64/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.97  --demod_completeness_check              fast
% 2.64/0.97  --demod_use_ground                      true
% 2.64/0.97  --sup_to_prop_solver                    passive
% 2.64/0.97  --sup_prop_simpl_new                    true
% 2.64/0.97  --sup_prop_simpl_given                  true
% 2.64/0.97  --sup_fun_splitting                     false
% 2.64/0.97  --sup_smt_interval                      50000
% 2.64/0.97  
% 2.64/0.97  ------ Superposition Simplification Setup
% 2.64/0.97  
% 2.64/0.97  --sup_indices_passive                   []
% 2.64/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.97  --sup_full_bw                           [BwDemod]
% 2.64/0.97  --sup_immed_triv                        [TrivRules]
% 2.64/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.97  --sup_immed_bw_main                     []
% 2.64/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.97  
% 2.64/0.97  ------ Combination Options
% 2.64/0.97  
% 2.64/0.97  --comb_res_mult                         3
% 2.64/0.97  --comb_sup_mult                         2
% 2.64/0.97  --comb_inst_mult                        10
% 2.64/0.97  
% 2.64/0.97  ------ Debug Options
% 2.64/0.97  
% 2.64/0.97  --dbg_backtrace                         false
% 2.64/0.97  --dbg_dump_prop_clauses                 false
% 2.64/0.97  --dbg_dump_prop_clauses_file            -
% 2.64/0.97  --dbg_out_stat                          false
% 2.64/0.97  
% 2.64/0.97  
% 2.64/0.97  
% 2.64/0.97  
% 2.64/0.97  ------ Proving...
% 2.64/0.97  
% 2.64/0.97  
% 2.64/0.97  % SZS status Theorem for theBenchmark.p
% 2.64/0.97  
% 2.64/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/0.97  
% 2.64/0.97  fof(f9,conjecture,(
% 2.64/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f10,negated_conjecture,(
% 2.64/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.64/0.97    inference(negated_conjecture,[],[f9])).
% 2.64/0.97  
% 2.64/0.97  fof(f22,plain,(
% 2.64/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f10])).
% 2.64/0.97  
% 2.64/0.97  fof(f23,plain,(
% 2.64/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.97    inference(flattening,[],[f22])).
% 2.64/0.97  
% 2.64/0.97  fof(f34,plain,(
% 2.64/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.97    inference(nnf_transformation,[],[f23])).
% 2.64/0.97  
% 2.64/0.97  fof(f35,plain,(
% 2.64/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.97    inference(flattening,[],[f34])).
% 2.64/0.97  
% 2.64/0.97  fof(f43,plain,(
% 2.64/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK8) | r1_tmap_1(X3,X0,X4,X6)) & sK8 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f42,plain,(
% 2.64/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK7)) & sK7 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK7,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f41,plain,(
% 2.64/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK6,u1_struct_0(X2)) & r2_hidden(X6,sK6) & v3_pre_topc(sK6,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f40,plain,(
% 2.64/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | ~r1_tmap_1(X3,X0,sK5,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X7) | r1_tmap_1(X3,X0,sK5,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f39,plain,(
% 2.64/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | ~r1_tmap_1(sK4,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X7) | r1_tmap_1(sK4,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f38,plain,(
% 2.64/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK3)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK3))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f37,plain,(
% 2.64/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK2) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f36,plain,(
% 2.64/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK1,X4,X6)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X7) | r1_tmap_1(X3,sK1,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f44,plain,(
% 2.64/0.97    ((((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK3)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK2) & m1_subset_1(sK8,u1_struct_0(sK3))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.64/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).
% 2.64/0.97  
% 2.64/0.97  fof(f80,plain,(
% 2.64/0.97    r1_tarski(sK6,u1_struct_0(sK3))),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f3,axiom,(
% 2.64/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f30,plain,(
% 2.64/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.64/0.97    inference(nnf_transformation,[],[f3])).
% 2.64/0.97  
% 2.64/0.97  fof(f52,plain,(
% 2.64/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f30])).
% 2.64/0.97  
% 2.64/0.97  fof(f82,plain,(
% 2.64/0.97    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | r1_tmap_1(sK4,sK1,sK5,sK7)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f81,plain,(
% 2.64/0.97    sK7 = sK8),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f7,axiom,(
% 2.64/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f18,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f7])).
% 2.64/0.97  
% 2.64/0.97  fof(f19,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.97    inference(flattening,[],[f18])).
% 2.64/0.97  
% 2.64/0.97  fof(f32,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.97    inference(nnf_transformation,[],[f19])).
% 2.64/0.97  
% 2.64/0.97  fof(f58,plain,(
% 2.64/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f32])).
% 2.64/0.97  
% 2.64/0.97  fof(f87,plain,(
% 2.64/0.97    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.97    inference(equality_resolution,[],[f58])).
% 2.64/0.97  
% 2.64/0.97  fof(f72,plain,(
% 2.64/0.97    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f71,plain,(
% 2.64/0.97    v1_funct_1(sK5)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f5,axiom,(
% 2.64/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f14,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f5])).
% 2.64/0.97  
% 2.64/0.97  fof(f15,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.97    inference(flattening,[],[f14])).
% 2.64/0.97  
% 2.64/0.97  fof(f55,plain,(
% 2.64/0.97    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f15])).
% 2.64/0.97  
% 2.64/0.97  fof(f69,plain,(
% 2.64/0.97    ~v2_struct_0(sK4)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f61,plain,(
% 2.64/0.97    ~v2_struct_0(sK1)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f62,plain,(
% 2.64/0.97    v2_pre_topc(sK1)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f63,plain,(
% 2.64/0.97    l1_pre_topc(sK1)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f73,plain,(
% 2.64/0.97    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f64,plain,(
% 2.64/0.97    ~v2_struct_0(sK2)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f65,plain,(
% 2.64/0.97    v2_pre_topc(sK2)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f66,plain,(
% 2.64/0.97    l1_pre_topc(sK2)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f67,plain,(
% 2.64/0.97    ~v2_struct_0(sK3)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f70,plain,(
% 2.64/0.97    m1_pre_topc(sK4,sK2)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f74,plain,(
% 2.64/0.97    m1_pre_topc(sK3,sK4)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f77,plain,(
% 2.64/0.97    m1_subset_1(sK8,u1_struct_0(sK3))),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f76,plain,(
% 2.64/0.97    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f57,plain,(
% 2.64/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f32])).
% 2.64/0.97  
% 2.64/0.97  fof(f88,plain,(
% 2.64/0.97    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.97    inference(equality_resolution,[],[f57])).
% 2.64/0.97  
% 2.64/0.97  fof(f6,axiom,(
% 2.64/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f16,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f6])).
% 2.64/0.97  
% 2.64/0.97  fof(f17,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.97    inference(flattening,[],[f16])).
% 2.64/0.97  
% 2.64/0.97  fof(f56,plain,(
% 2.64/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f17])).
% 2.64/0.97  
% 2.64/0.97  fof(f86,plain,(
% 2.64/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.97    inference(equality_resolution,[],[f56])).
% 2.64/0.97  
% 2.64/0.97  fof(f83,plain,(
% 2.64/0.97    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK1,sK5,sK7)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f4,axiom,(
% 2.64/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f12,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f4])).
% 2.64/0.97  
% 2.64/0.97  fof(f13,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.97    inference(flattening,[],[f12])).
% 2.64/0.97  
% 2.64/0.97  fof(f31,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.97    inference(nnf_transformation,[],[f13])).
% 2.64/0.97  
% 2.64/0.97  fof(f54,plain,(
% 2.64/0.97    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f31])).
% 2.64/0.97  
% 2.64/0.97  fof(f1,axiom,(
% 2.64/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f11,plain,(
% 2.64/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f1])).
% 2.64/0.97  
% 2.64/0.97  fof(f24,plain,(
% 2.64/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.64/0.97    inference(nnf_transformation,[],[f11])).
% 2.64/0.97  
% 2.64/0.97  fof(f25,plain,(
% 2.64/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.64/0.97    inference(rectify,[],[f24])).
% 2.64/0.97  
% 2.64/0.97  fof(f26,plain,(
% 2.64/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.64/0.97    introduced(choice_axiom,[])).
% 2.64/0.97  
% 2.64/0.97  fof(f27,plain,(
% 2.64/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.64/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.64/0.97  
% 2.64/0.97  fof(f46,plain,(
% 2.64/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f27])).
% 2.64/0.97  
% 2.64/0.97  fof(f45,plain,(
% 2.64/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f27])).
% 2.64/0.97  
% 2.64/0.97  fof(f47,plain,(
% 2.64/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f27])).
% 2.64/0.97  
% 2.64/0.97  fof(f8,axiom,(
% 2.64/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ((X3 = X4 & r1_tarski(X3,X2) & r1_tarski(X2,u1_struct_0(X1)) & v3_pre_topc(X2,X0)) => (v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0))))))))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f20,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | (X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.97    inference(ennf_transformation,[],[f8])).
% 2.64/0.97  
% 2.64/0.97  fof(f21,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.97    inference(flattening,[],[f20])).
% 2.64/0.97  
% 2.64/0.97  fof(f33,plain,(
% 2.64/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) | ~v3_pre_topc(X3,X0)) & (v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X1))) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.97    inference(nnf_transformation,[],[f21])).
% 2.64/0.97  
% 2.64/0.97  fof(f60,plain,(
% 2.64/0.97    ( ! [X4,X2,X0,X3,X1] : (v3_pre_topc(X4,X1) | ~v3_pre_topc(X3,X0) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.97    inference(cnf_transformation,[],[f33])).
% 2.64/0.97  
% 2.64/0.97  fof(f89,plain,(
% 2.64/0.97    ( ! [X4,X2,X0,X1] : (v3_pre_topc(X4,X1) | ~v3_pre_topc(X4,X0) | ~r1_tarski(X4,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.97    inference(equality_resolution,[],[f60])).
% 2.64/0.97  
% 2.64/0.97  fof(f2,axiom,(
% 2.64/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.64/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/0.97  
% 2.64/0.97  fof(f28,plain,(
% 2.64/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.64/0.97    inference(nnf_transformation,[],[f2])).
% 2.64/0.97  
% 2.64/0.97  fof(f29,plain,(
% 2.64/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.64/0.97    inference(flattening,[],[f28])).
% 2.64/0.97  
% 2.64/0.97  fof(f48,plain,(
% 2.64/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.64/0.97    inference(cnf_transformation,[],[f29])).
% 2.64/0.97  
% 2.64/0.97  fof(f85,plain,(
% 2.64/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.64/0.97    inference(equality_resolution,[],[f48])).
% 2.64/0.97  
% 2.64/0.97  fof(f79,plain,(
% 2.64/0.97    r2_hidden(sK7,sK6)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f78,plain,(
% 2.64/0.97    v3_pre_topc(sK6,sK2)),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  fof(f75,plain,(
% 2.64/0.97    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.64/0.97    inference(cnf_transformation,[],[f44])).
% 2.64/0.97  
% 2.64/0.97  cnf(c_19,negated_conjecture,
% 2.64/0.97      ( r1_tarski(sK6,u1_struct_0(sK3)) ),
% 2.64/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1889,plain,
% 2.64/0.97      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6,plain,
% 2.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1898,plain,
% 2.64/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.64/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_17,negated_conjecture,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK7)
% 2.64/0.97      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 2.64/0.97      inference(cnf_transformation,[],[f82]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1890,plain,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_18,negated_conjecture,
% 2.64/0.97      ( sK7 = sK8 ),
% 2.64/0.97      inference(cnf_transformation,[],[f81]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1974,plain,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) = iProver_top ),
% 2.64/0.97      inference(light_normalisation,[status(thm)],[c_1890,c_18]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_12,plain,
% 2.64/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.64/0.97      | ~ v3_pre_topc(X6,X0)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.64/0.97      | ~ r2_hidden(X3,X6)
% 2.64/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f87]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_27,negated_conjecture,
% 2.64/0.97      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 2.64/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_547,plain,
% 2.64/0.97      ( r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ v3_pre_topc(X6,X0)
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.64/0.97      | ~ r2_hidden(X3,X6)
% 2.64/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5)
% 2.64/0.97      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.64/0.97      | sK5 != X2 ),
% 2.64/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_548,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ v3_pre_topc(X5,X3)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | ~ r2_hidden(X4,X5)
% 2.64/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | ~ v1_funct_1(sK5)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(unflattening,[status(thm)],[c_547]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_28,negated_conjecture,
% 2.64/0.97      ( v1_funct_1(sK5) ),
% 2.64/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_552,plain,
% 2.64/0.97      ( v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.64/0.97      | ~ r2_hidden(X4,X5)
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ v3_pre_topc(X5,X3)
% 2.64/0.97      | r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_548,c_28]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_553,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ v3_pre_topc(X5,X3)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | ~ r2_hidden(X4,X5)
% 2.64/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_552]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_10,plain,
% 2.64/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.64/0.97      | ~ m1_pre_topc(X2,X0)
% 2.64/0.97      | m1_pre_topc(X2,X1)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_602,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ v3_pre_topc(X5,X3)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | ~ r2_hidden(X4,X5)
% 2.64/0.97      | ~ r1_tarski(X5,u1_struct_0(X0))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(forward_subsumption_resolution,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_553,c_10]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1870,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.64/0.97      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) != iProver_top
% 2.64/0.97      | r1_tmap_1(X0,X1,sK5,X4) = iProver_top
% 2.64/0.97      | v3_pre_topc(X5,X0) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,X3) != iProver_top
% 2.64/0.97      | m1_pre_topc(X2,X0) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.64/0.97      | r2_hidden(X4,X5) != iProver_top
% 2.64/0.97      | r1_tarski(X5,u1_struct_0(X2)) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X3) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | v2_pre_topc(X3) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X3) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2379,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.64/0.97      | v3_pre_topc(X4,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | r2_hidden(X3,X4) != iProver_top
% 2.64/0.97      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(sK4) = iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.64/0.97      inference(equality_resolution,[status(thm)],[c_1870]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_30,negated_conjecture,
% 2.64/0.97      ( ~ v2_struct_0(sK4) ),
% 2.64/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_47,plain,
% 2.64/0.97      ( v2_struct_0(sK4) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_984,plain,( X0 = X0 ),theory(equality) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2222,plain,
% 2.64/0.97      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.64/0.97      inference(instantiation,[status(thm)],[c_984]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2223,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK4,X0,sK5),X3)
% 2.64/0.97      | r1_tmap_1(sK4,X1,sK5,X3)
% 2.64/0.97      | ~ v3_pre_topc(X4,sK4)
% 2.64/0.97      | ~ m1_pre_topc(X0,sK4)
% 2.64/0.97      | ~ m1_pre_topc(sK4,X2)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(sK4))
% 2.64/0.97      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 2.64/0.97      | ~ r2_hidden(X3,X4)
% 2.64/0.97      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | v2_struct_0(sK4)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.64/0.97      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 2.64/0.97      inference(instantiation,[status(thm)],[c_602]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2229,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.64/0.97      | v3_pre_topc(X4,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | r2_hidden(X3,X4) != iProver_top
% 2.64/0.97      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(sK4) = iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_2223]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3266,plain,
% 2.64/0.97      ( v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | r2_hidden(X3,X4) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | v3_pre_topc(X4,sK4) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.64/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_2379,c_47,c_2222,c_2229]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3267,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) = iProver_top
% 2.64/0.97      | v3_pre_topc(X4,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | r2_hidden(X3,X4) != iProver_top
% 2.64/0.97      | r1_tarski(X4,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_3266]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3291,plain,
% 2.64/0.97      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
% 2.64/0.97      | v3_pre_topc(X3,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X1) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.64/0.97      | r2_hidden(X2,X3) != iProver_top
% 2.64/0.97      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(sK1) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | v2_pre_topc(sK1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 2.64/0.97      inference(equality_resolution,[status(thm)],[c_3267]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_38,negated_conjecture,
% 2.64/0.97      ( ~ v2_struct_0(sK1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_39,plain,
% 2.64/0.97      ( v2_struct_0(sK1) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_37,negated_conjecture,
% 2.64/0.97      ( v2_pre_topc(sK1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_40,plain,
% 2.64/0.97      ( v2_pre_topc(sK1) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_36,negated_conjecture,
% 2.64/0.97      ( l1_pre_topc(sK1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_41,plain,
% 2.64/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_26,negated_conjecture,
% 2.64/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 2.64/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_51,plain,
% 2.64/0.97      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6057,plain,
% 2.64/0.97      ( l1_pre_topc(X1) != iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | r2_hidden(X2,X3) != iProver_top
% 2.64/0.97      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
% 2.64/0.97      | v3_pre_topc(X3,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X1) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_3291,c_39,c_40,c_41,c_51]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6058,plain,
% 2.64/0.97      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,sK1,sK5,X2) = iProver_top
% 2.64/0.97      | v3_pre_topc(X3,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X1) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | r2_hidden(X2,X3) != iProver_top
% 2.64/0.97      | r1_tarski(X3,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_6057]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6077,plain,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK8) = iProver_top
% 2.64/0.97      | v3_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.64/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.64/0.97      | r2_hidden(sK8,X0) != iProver_top
% 2.64/0.97      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.64/0.97      | v2_struct_0(sK2) = iProver_top
% 2.64/0.97      | v2_struct_0(sK3) = iProver_top
% 2.64/0.97      | v2_pre_topc(sK2) != iProver_top
% 2.64/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_1974,c_6058]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_35,negated_conjecture,
% 2.64/0.97      ( ~ v2_struct_0(sK2) ),
% 2.64/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_42,plain,
% 2.64/0.97      ( v2_struct_0(sK2) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_34,negated_conjecture,
% 2.64/0.97      ( v2_pre_topc(sK2) ),
% 2.64/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_43,plain,
% 2.64/0.97      ( v2_pre_topc(sK2) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_33,negated_conjecture,
% 2.64/0.97      ( l1_pre_topc(sK2) ),
% 2.64/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_44,plain,
% 2.64/0.97      ( l1_pre_topc(sK2) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_32,negated_conjecture,
% 2.64/0.97      ( ~ v2_struct_0(sK3) ),
% 2.64/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_45,plain,
% 2.64/0.97      ( v2_struct_0(sK3) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_29,negated_conjecture,
% 2.64/0.97      ( m1_pre_topc(sK4,sK2) ),
% 2.64/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_48,plain,
% 2.64/0.97      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_25,negated_conjecture,
% 2.64/0.97      ( m1_pre_topc(sK3,sK4) ),
% 2.64/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_52,plain,
% 2.64/0.97      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_22,negated_conjecture,
% 2.64/0.97      ( m1_subset_1(sK8,u1_struct_0(sK3)) ),
% 2.64/0.97      inference(cnf_transformation,[],[f77]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_55,plain,
% 2.64/0.97      ( m1_subset_1(sK8,u1_struct_0(sK3)) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_23,negated_conjecture,
% 2.64/0.97      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.64/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1885,plain,
% 2.64/0.97      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1935,plain,
% 2.64/0.97      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.64/0.97      inference(light_normalisation,[status(thm)],[c_1885,c_18]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_13,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.64/0.97      | ~ v3_pre_topc(X6,X0)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.64/0.97      | ~ r2_hidden(X3,X6)
% 2.64/0.97      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f88]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_11,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f86]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_194,plain,
% 2.64/0.97      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1) ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_13,c_11]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_195,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5) ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_194]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_481,plain,
% 2.64/0.97      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.64/0.97      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.64/0.97      | ~ m1_pre_topc(X0,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X5)
% 2.64/0.97      | ~ m1_pre_topc(X4,X0)
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.64/0.97      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X5)
% 2.64/0.97      | v2_struct_0(X4)
% 2.64/0.97      | ~ v1_funct_1(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X5)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X5)
% 2.64/0.97      | u1_struct_0(X0) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.64/0.97      | sK5 != X2 ),
% 2.64/0.97      inference(resolution_lifted,[status(thm)],[c_195,c_27]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_482,plain,
% 2.64/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | ~ v1_funct_1(sK5)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(unflattening,[status(thm)],[c_481]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_486,plain,
% 2.64/0.97      ( v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_482,c_28]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_487,plain,
% 2.64/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_486]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_528,plain,
% 2.64/0.97      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 2.64/0.97      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 2.64/0.97      | ~ m1_pre_topc(X3,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X3)
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.64/0.97      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.64/0.97      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.64/0.97      | v2_struct_0(X0)
% 2.64/0.97      | v2_struct_0(X1)
% 2.64/0.97      | v2_struct_0(X3)
% 2.64/0.97      | v2_struct_0(X2)
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ v2_pre_topc(X1)
% 2.64/0.97      | ~ l1_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X1)
% 2.64/0.97      | u1_struct_0(X3) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.64/0.97      inference(forward_subsumption_resolution,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_487,c_10]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1871,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK4)
% 2.64/0.97      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.64/0.97      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK5),X4) = iProver_top
% 2.64/0.97      | r1_tmap_1(X0,X1,sK5,X4) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,X3) != iProver_top
% 2.64/0.97      | m1_pre_topc(X2,X0) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.64/0.97      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X3) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | v2_pre_topc(X3) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X3) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2883,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(sK4) = iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.64/0.97      inference(equality_resolution,[status(thm)],[c_1871]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3218,plain,
% 2.64/0.97      ( v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.64/0.97      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_2883,c_47,c_2222,c_2225]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3219,plain,
% 2.64/0.97      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.64/0.97      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK4,X1,sK5),X3) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,X0,sK5,X3) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X2) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.64/0.97      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X2) = iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | v2_pre_topc(X0) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_3218]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3239,plain,
% 2.64/0.97      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X1) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(sK1) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | v2_pre_topc(sK1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 2.64/0.97      inference(equality_resolution,[status(thm)],[c_3219]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3296,plain,
% 2.64/0.97      ( l1_pre_topc(X1) != iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X1) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_3239,c_39,c_40,c_41,c_51]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3297,plain,
% 2.64/0.97      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK4,X0,sK5),X2) = iProver_top
% 2.64/0.97      | r1_tmap_1(sK4,sK1,sK5,X2) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,X1) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.64/0.97      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | v2_struct_0(X1) = iProver_top
% 2.64/0.97      | v2_struct_0(X0) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top ),
% 2.64/0.97      inference(renaming,[status(thm)],[c_3296]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_16,negated_conjecture,
% 2.64/0.97      ( ~ r1_tmap_1(sK4,sK1,sK5,sK7)
% 2.64/0.97      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) ),
% 2.64/0.97      inference(cnf_transformation,[],[f83]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1891,plain,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1979,plain,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 2.64/0.97      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK8) != iProver_top ),
% 2.64/0.97      inference(light_normalisation,[status(thm)],[c_1891,c_18]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3312,plain,
% 2.64/0.97      ( r1_tmap_1(sK4,sK1,sK5,sK8) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.64/0.97      | m1_pre_topc(sK3,sK4) != iProver_top
% 2.64/0.97      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | m1_subset_1(sK8,u1_struct_0(sK3)) != iProver_top
% 2.64/0.97      | v2_struct_0(sK2) = iProver_top
% 2.64/0.97      | v2_struct_0(sK3) = iProver_top
% 2.64/0.97      | v2_pre_topc(sK2) != iProver_top
% 2.64/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_3297,c_1979]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6396,plain,
% 2.64/0.97      ( v3_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.97      | r2_hidden(sK8,X0) != iProver_top
% 2.64/0.97      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_6077,c_42,c_43,c_44,c_45,c_48,c_52,c_55,c_1935,c_3312]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6406,plain,
% 2.64/0.97      ( v3_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | r2_hidden(sK8,X0) != iProver_top
% 2.64/0.97      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top
% 2.64/0.97      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_1898,c_6396]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6670,plain,
% 2.64/0.97      ( v3_pre_topc(sK6,sK4) != iProver_top
% 2.64/0.97      | r2_hidden(sK8,sK6) != iProver_top
% 2.64/0.97      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_1889,c_6406]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1881,plain,
% 2.64/0.97      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_8,plain,
% 2.64/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.64/0.97      | ~ m1_pre_topc(X1,X2)
% 2.64/0.97      | ~ m1_pre_topc(X0,X2)
% 2.64/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.64/0.97      | ~ v2_pre_topc(X2)
% 2.64/0.97      | ~ l1_pre_topc(X2) ),
% 2.64/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1896,plain,
% 2.64/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,X2) != iProver_top
% 2.64/0.97      | m1_pre_topc(X0,X2) != iProver_top
% 2.64/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1894,plain,
% 2.64/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 2.64/0.97      | m1_pre_topc(X2,X0) != iProver_top
% 2.64/0.97      | m1_pre_topc(X2,X1) = iProver_top
% 2.64/0.97      | v2_pre_topc(X1) != iProver_top
% 2.64/0.97      | l1_pre_topc(X1) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2012,plain,
% 2.64/0.97      ( m1_pre_topc(X0,X1) != iProver_top
% 2.64/0.97      | m1_pre_topc(X1,X2) != iProver_top
% 2.64/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.64/0.97      | v2_pre_topc(X2) != iProver_top
% 2.64/0.97      | l1_pre_topc(X2) != iProver_top ),
% 2.64/0.97      inference(forward_subsumption_resolution,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_1896,c_1894]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_5440,plain,
% 2.64/0.97      ( m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top
% 2.64/0.97      | v2_pre_topc(sK2) != iProver_top
% 2.64/0.97      | l1_pre_topc(sK2) != iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_1881,c_2012]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_5840,plain,
% 2.64/0.97      ( m1_pre_topc(X0,sK4) != iProver_top
% 2.64/0.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) = iProver_top ),
% 2.64/0.97      inference(global_propositional_subsumption,
% 2.64/0.97                [status(thm)],
% 2.64/0.97                [c_5440,c_43,c_44]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1,plain,
% 2.64/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.64/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1902,plain,
% 2.64/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.64/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_2,plain,
% 2.64/0.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.64/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_1901,plain,
% 2.64/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.64/0.97      | r2_hidden(X0,X2) = iProver_top
% 2.64/0.97      | r1_tarski(X1,X2) != iProver_top ),
% 2.64/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_3752,plain,
% 2.64/0.97      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.64/0.97      | r1_tarski(X0,X2) != iProver_top
% 2.64/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_1902,c_1901]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_5480,plain,
% 2.64/0.97      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.64/0.97      | r1_tarski(X0,X3) != iProver_top
% 2.64/0.97      | r1_tarski(X3,X2) != iProver_top
% 2.64/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.64/0.97      inference(superposition,[status(thm)],[c_3752,c_1901]) ).
% 2.64/0.97  
% 2.64/0.97  cnf(c_6232,plain,
% 2.64/0.97      ( r2_hidden(sK0(sK6,X0),X1) = iProver_top
% 2.64/0.97      | r1_tarski(u1_struct_0(sK3),X1) != iProver_top
% 2.64/0.98      | r1_tarski(sK6,X0) = iProver_top ),
% 2.64/0.98      inference(superposition,[status(thm)],[c_1889,c_5480]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_0,plain,
% 2.64/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.64/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1903,plain,
% 2.64/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.64/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6377,plain,
% 2.64/0.98      ( r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 2.64/0.98      | r1_tarski(sK6,X0) = iProver_top ),
% 2.64/0.98      inference(superposition,[status(thm)],[c_6232,c_1903]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_6471,plain,
% 2.64/0.98      ( m1_pre_topc(sK3,sK4) != iProver_top
% 2.64/0.98      | r1_tarski(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.64/0.98      inference(superposition,[status(thm)],[c_5840,c_6377]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4746,plain,
% 2.64/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.64/0.98      | ~ r1_tarski(sK6,u1_struct_0(sK4)) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_4747,plain,
% 2.64/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.64/0.98      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_4746]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_14,plain,
% 2.64/0.98      ( ~ v3_pre_topc(X0,X1)
% 2.64/0.98      | ~ v3_pre_topc(X2,X1)
% 2.64/0.98      | v3_pre_topc(X0,X3)
% 2.64/0.98      | ~ m1_pre_topc(X3,X1)
% 2.64/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X3)))
% 2.64/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/0.98      | ~ r1_tarski(X0,X2)
% 2.64/0.98      | ~ r1_tarski(X2,u1_struct_0(X3))
% 2.64/0.98      | ~ v2_pre_topc(X1)
% 2.64/0.98      | ~ l1_pre_topc(X1) ),
% 2.64/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_2347,plain,
% 2.64/0.98      ( ~ v3_pre_topc(X0,sK2)
% 2.64/0.98      | v3_pre_topc(sK6,X1)
% 2.64/0.98      | ~ v3_pre_topc(sK6,sK2)
% 2.64/0.98      | ~ m1_pre_topc(X1,sK2)
% 2.64/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.64/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X1)))
% 2.64/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.64/0.98      | ~ r1_tarski(X0,u1_struct_0(X1))
% 2.64/0.98      | ~ r1_tarski(sK6,X0)
% 2.64/0.98      | ~ v2_pre_topc(sK2)
% 2.64/0.98      | ~ l1_pre_topc(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_2616,plain,
% 2.64/0.98      ( v3_pre_topc(sK6,X0)
% 2.64/0.98      | ~ v3_pre_topc(sK6,sK2)
% 2.64/0.98      | ~ m1_pre_topc(X0,sK2)
% 2.64/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.64/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.64/0.98      | ~ r1_tarski(sK6,u1_struct_0(X0))
% 2.64/0.98      | ~ r1_tarski(sK6,sK6)
% 2.64/0.98      | ~ v2_pre_topc(sK2)
% 2.64/0.98      | ~ l1_pre_topc(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_2347]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3314,plain,
% 2.64/0.98      ( v3_pre_topc(sK6,sK4)
% 2.64/0.98      | ~ v3_pre_topc(sK6,sK2)
% 2.64/0.98      | ~ m1_pre_topc(sK4,sK2)
% 2.64/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.64/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.64/0.98      | ~ r1_tarski(sK6,u1_struct_0(sK4))
% 2.64/0.98      | ~ r1_tarski(sK6,sK6)
% 2.64/0.98      | ~ v2_pre_topc(sK2)
% 2.64/0.98      | ~ l1_pre_topc(sK2) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_2616]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_3315,plain,
% 2.64/0.98      ( v3_pre_topc(sK6,sK4) = iProver_top
% 2.64/0.98      | v3_pre_topc(sK6,sK2) != iProver_top
% 2.64/0.98      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.64/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.64/0.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.64/0.98      | r1_tarski(sK6,u1_struct_0(sK4)) != iProver_top
% 2.64/0.98      | r1_tarski(sK6,sK6) != iProver_top
% 2.64/0.98      | v2_pre_topc(sK2) != iProver_top
% 2.64/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_3314]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_5,plain,
% 2.64/0.98      ( r1_tarski(X0,X0) ),
% 2.64/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_2950,plain,
% 2.64/0.98      ( r1_tarski(sK6,sK6) ),
% 2.64/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_2951,plain,
% 2.64/0.98      ( r1_tarski(sK6,sK6) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_2950]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_20,negated_conjecture,
% 2.64/0.98      ( r2_hidden(sK7,sK6) ),
% 2.64/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1888,plain,
% 2.64/0.98      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_1930,plain,
% 2.64/0.98      ( r2_hidden(sK8,sK6) = iProver_top ),
% 2.64/0.98      inference(light_normalisation,[status(thm)],[c_1888,c_18]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_21,negated_conjecture,
% 2.64/0.98      ( v3_pre_topc(sK6,sK2) ),
% 2.64/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_56,plain,
% 2.64/0.98      ( v3_pre_topc(sK6,sK2) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_24,negated_conjecture,
% 2.64/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.64/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(c_53,plain,
% 2.64/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.64/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.64/0.98  
% 2.64/0.98  cnf(contradiction,plain,
% 2.64/0.98      ( $false ),
% 2.64/0.98      inference(minisat,
% 2.64/0.98                [status(thm)],
% 2.64/0.98                [c_6670,c_6471,c_4747,c_3315,c_2951,c_1930,c_56,c_53,
% 2.64/0.98                 c_52,c_48,c_44,c_43]) ).
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/0.98  
% 2.64/0.98  ------                               Statistics
% 2.64/0.98  
% 2.64/0.98  ------ General
% 2.64/0.98  
% 2.64/0.98  abstr_ref_over_cycles:                  0
% 2.64/0.98  abstr_ref_under_cycles:                 0
% 2.64/0.98  gc_basic_clause_elim:                   0
% 2.64/0.98  forced_gc_time:                         0
% 2.64/0.98  parsing_time:                           0.01
% 2.64/0.98  unif_index_cands_time:                  0.
% 2.64/0.98  unif_index_add_time:                    0.
% 2.64/0.98  orderings_time:                         0.
% 2.64/0.98  out_proof_time:                         0.016
% 2.64/0.98  total_time:                             0.209
% 2.64/0.98  num_of_symbols:                         55
% 2.64/0.98  num_of_terms:                           4187
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing
% 2.64/0.98  
% 2.64/0.98  num_of_splits:                          0
% 2.64/0.98  num_of_split_atoms:                     0
% 2.64/0.98  num_of_reused_defs:                     0
% 2.64/0.98  num_eq_ax_congr_red:                    6
% 2.64/0.98  num_of_sem_filtered_clauses:            1
% 2.64/0.98  num_of_subtypes:                        0
% 2.64/0.98  monotx_restored_types:                  0
% 2.64/0.98  sat_num_of_epr_types:                   0
% 2.64/0.98  sat_num_of_non_cyclic_types:            0
% 2.64/0.98  sat_guarded_non_collapsed_types:        0
% 2.64/0.98  num_pure_diseq_elim:                    0
% 2.64/0.98  simp_replaced_by:                       0
% 2.64/0.98  res_preprocessed:                       174
% 2.64/0.98  prep_upred:                             0
% 2.64/0.98  prep_unflattend:                        3
% 2.64/0.98  smt_new_axioms:                         0
% 2.64/0.98  pred_elim_cands:                        9
% 2.64/0.98  pred_elim:                              2
% 2.64/0.98  pred_elim_cl:                           3
% 2.64/0.98  pred_elim_cycles:                       4
% 2.64/0.98  merged_defs:                            16
% 2.64/0.98  merged_defs_ncl:                        0
% 2.64/0.98  bin_hyper_res:                          16
% 2.64/0.98  prep_cycles:                            4
% 2.64/0.98  pred_elim_time:                         0.009
% 2.64/0.98  splitting_time:                         0.
% 2.64/0.98  sem_filter_time:                        0.
% 2.64/0.98  monotx_time:                            0.001
% 2.64/0.98  subtype_inf_time:                       0.
% 2.64/0.98  
% 2.64/0.98  ------ Problem properties
% 2.64/0.98  
% 2.64/0.98  clauses:                                35
% 2.64/0.98  conjectures:                            21
% 2.64/0.98  epr:                                    18
% 2.64/0.98  horn:                                   31
% 2.64/0.98  ground:                                 21
% 2.64/0.98  unary:                                  20
% 2.64/0.98  binary:                                 6
% 2.64/0.98  lits:                                   115
% 2.64/0.98  lits_eq:                                6
% 2.64/0.98  fd_pure:                                0
% 2.64/0.98  fd_pseudo:                              0
% 2.64/0.98  fd_cond:                                0
% 2.64/0.98  fd_pseudo_cond:                         1
% 2.64/0.98  ac_symbols:                             0
% 2.64/0.98  
% 2.64/0.98  ------ Propositional Solver
% 2.64/0.98  
% 2.64/0.98  prop_solver_calls:                      27
% 2.64/0.98  prop_fast_solver_calls:                 1749
% 2.64/0.98  smt_solver_calls:                       0
% 2.64/0.98  smt_fast_solver_calls:                  0
% 2.64/0.98  prop_num_of_clauses:                    2040
% 2.64/0.98  prop_preprocess_simplified:             6576
% 2.64/0.98  prop_fo_subsumed:                       59
% 2.64/0.98  prop_solver_time:                       0.
% 2.64/0.98  smt_solver_time:                        0.
% 2.64/0.98  smt_fast_solver_time:                   0.
% 2.64/0.98  prop_fast_solver_time:                  0.
% 2.64/0.98  prop_unsat_core_time:                   0.
% 2.64/0.98  
% 2.64/0.98  ------ QBF
% 2.64/0.98  
% 2.64/0.98  qbf_q_res:                              0
% 2.64/0.98  qbf_num_tautologies:                    0
% 2.64/0.98  qbf_prep_cycles:                        0
% 2.64/0.98  
% 2.64/0.98  ------ BMC1
% 2.64/0.98  
% 2.64/0.98  bmc1_current_bound:                     -1
% 2.64/0.98  bmc1_last_solved_bound:                 -1
% 2.64/0.98  bmc1_unsat_core_size:                   -1
% 2.64/0.98  bmc1_unsat_core_parents_size:           -1
% 2.64/0.98  bmc1_merge_next_fun:                    0
% 2.64/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.64/0.98  
% 2.64/0.98  ------ Instantiation
% 2.64/0.98  
% 2.64/0.98  inst_num_of_clauses:                    640
% 2.64/0.98  inst_num_in_passive:                    122
% 2.64/0.98  inst_num_in_active:                     320
% 2.64/0.98  inst_num_in_unprocessed:                198
% 2.64/0.98  inst_num_of_loops:                      390
% 2.64/0.98  inst_num_of_learning_restarts:          0
% 2.64/0.98  inst_num_moves_active_passive:          68
% 2.64/0.98  inst_lit_activity:                      0
% 2.64/0.98  inst_lit_activity_moves:                0
% 2.64/0.98  inst_num_tautologies:                   0
% 2.64/0.98  inst_num_prop_implied:                  0
% 2.64/0.98  inst_num_existing_simplified:           0
% 2.64/0.98  inst_num_eq_res_simplified:             0
% 2.64/0.98  inst_num_child_elim:                    0
% 2.64/0.98  inst_num_of_dismatching_blockings:      134
% 2.64/0.98  inst_num_of_non_proper_insts:           572
% 2.64/0.98  inst_num_of_duplicates:                 0
% 2.64/0.98  inst_inst_num_from_inst_to_res:         0
% 2.64/0.98  inst_dismatching_checking_time:         0.
% 2.64/0.98  
% 2.64/0.98  ------ Resolution
% 2.64/0.98  
% 2.64/0.98  res_num_of_clauses:                     0
% 2.64/0.98  res_num_in_passive:                     0
% 2.64/0.98  res_num_in_active:                      0
% 2.64/0.98  res_num_of_loops:                       178
% 2.64/0.98  res_forward_subset_subsumed:            90
% 2.64/0.98  res_backward_subset_subsumed:           0
% 2.64/0.98  res_forward_subsumed:                   0
% 2.64/0.98  res_backward_subsumed:                  0
% 2.64/0.98  res_forward_subsumption_resolution:     2
% 2.64/0.98  res_backward_subsumption_resolution:    0
% 2.64/0.98  res_clause_to_clause_subsumption:       438
% 2.64/0.98  res_orphan_elimination:                 0
% 2.64/0.98  res_tautology_del:                      66
% 2.64/0.98  res_num_eq_res_simplified:              0
% 2.64/0.98  res_num_sel_changes:                    0
% 2.64/0.98  res_moves_from_active_to_pass:          0
% 2.64/0.98  
% 2.64/0.98  ------ Superposition
% 2.64/0.98  
% 2.64/0.98  sup_time_total:                         0.
% 2.64/0.98  sup_time_generating:                    0.
% 2.64/0.98  sup_time_sim_full:                      0.
% 2.64/0.98  sup_time_sim_immed:                     0.
% 2.64/0.98  
% 2.64/0.98  sup_num_of_clauses:                     93
% 2.64/0.98  sup_num_in_active:                      77
% 2.64/0.98  sup_num_in_passive:                     16
% 2.64/0.98  sup_num_of_loops:                       77
% 2.64/0.98  sup_fw_superposition:                   66
% 2.64/0.98  sup_bw_superposition:                   34
% 2.64/0.98  sup_immediate_simplified:               12
% 2.64/0.98  sup_given_eliminated:                   0
% 2.64/0.98  comparisons_done:                       0
% 2.64/0.98  comparisons_avoided:                    0
% 2.64/0.98  
% 2.64/0.98  ------ Simplifications
% 2.64/0.98  
% 2.64/0.98  
% 2.64/0.98  sim_fw_subset_subsumed:                 11
% 2.64/0.98  sim_bw_subset_subsumed:                 6
% 2.64/0.98  sim_fw_subsumed:                        1
% 2.64/0.98  sim_bw_subsumed:                        0
% 2.64/0.98  sim_fw_subsumption_res:                 1
% 2.64/0.98  sim_bw_subsumption_res:                 0
% 2.64/0.98  sim_tautology_del:                      10
% 2.64/0.98  sim_eq_tautology_del:                   4
% 2.64/0.98  sim_eq_res_simp:                        0
% 2.64/0.98  sim_fw_demodulated:                     0
% 2.64/0.98  sim_bw_demodulated:                     0
% 2.64/0.98  sim_light_normalised:                   4
% 2.64/0.98  sim_joinable_taut:                      0
% 2.64/0.98  sim_joinable_simp:                      0
% 2.64/0.98  sim_ac_normalised:                      0
% 2.64/0.98  sim_smt_subsumption:                    0
% 2.64/0.98  
%------------------------------------------------------------------------------
