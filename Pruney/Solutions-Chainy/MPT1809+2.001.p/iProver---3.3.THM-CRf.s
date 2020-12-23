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
% DateTime   : Thu Dec  3 12:24:15 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1677)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( ( X5 = X7
                                        & X5 = X6 )
                                     => ( r1_tmap_1(X0,X1,X2,X5)
                                      <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X4))
                                     => ( ( X5 = X7
                                          & X5 = X6 )
                                       => ( r1_tmap_1(X0,X1,X2,X5)
                                        <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
          ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
            | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
            | ~ r1_tmap_1(X0,X1,X2,X5) )
          & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
            | r1_tmap_1(X0,X1,X2,X5) )
          & X5 = X7
          & X5 = X6
          & m1_subset_1(X7,u1_struct_0(X4)) )
     => ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
          | ~ r1_tmap_1(X0,X1,X2,X5) )
        & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7)
            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
          | r1_tmap_1(X0,X1,X2,X5) )
        & sK7 = X5
        & X5 = X6
        & m1_subset_1(sK7,u1_struct_0(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                | ~ r1_tmap_1(X0,X1,X2,X5) )
              & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                | r1_tmap_1(X0,X1,X2,X5) )
              & X5 = X7
              & X5 = X6
              & m1_subset_1(X7,u1_struct_0(X4)) )
          & m1_subset_1(X6,u1_struct_0(X3)) )
     => ( ? [X7] :
            ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)
              | ~ r1_tmap_1(X0,X1,X2,X5) )
            & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) )
              | r1_tmap_1(X0,X1,X2,X5) )
            & X5 = X7
            & sK6 = X5
            & m1_subset_1(X7,u1_struct_0(X4)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                    | r1_tmap_1(X0,X1,X2,X5) )
                  & X5 = X7
                  & X5 = X6
                  & m1_subset_1(X7,u1_struct_0(X4)) )
              & m1_subset_1(X6,u1_struct_0(X3)) )
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                  | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                  | ~ r1_tmap_1(X0,X1,X2,sK5) )
                & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                    & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                  | r1_tmap_1(X0,X1,X2,sK5) )
                & sK5 = X7
                & sK5 = X6
                & m1_subset_1(X7,u1_struct_0(X4)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                        | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                        | ~ r1_tmap_1(X0,X1,X2,X5) )
                      & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                        | r1_tmap_1(X0,X1,X2,X5) )
                      & X5 = X7
                      & X5 = X6
                      & m1_subset_1(X7,u1_struct_0(X4)) )
                  & m1_subset_1(X6,u1_struct_0(X3)) )
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & k1_tsep_1(X0,X3,X4) = X0
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7)
                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                    & ( ( r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7)
                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                      | r1_tmap_1(X0,X1,X2,X5) )
                    & X5 = X7
                    & X5 = X6
                    & m1_subset_1(X7,u1_struct_0(sK4)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & k1_tsep_1(X0,X3,sK4) = X0
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                            | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                            | ~ r1_tmap_1(X0,X1,X2,X5) )
                          & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                            | r1_tmap_1(X0,X1,X2,X5) )
                          & X5 = X7
                          & X5 = X6
                          & m1_subset_1(X7,u1_struct_0(X4)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & k1_tsep_1(X0,X3,X4) = X0
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                          | ~ r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)
                          | ~ r1_tmap_1(X0,X1,X2,X5) )
                        & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                            & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) )
                          | r1_tmap_1(X0,X1,X2,X5) )
                        & X5 = X7
                        & X5 = X6
                        & m1_subset_1(X7,u1_struct_0(X4)) )
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & k1_tsep_1(X0,sK3,X4) = X0
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                | ~ r1_tmap_1(X0,X1,X2,X5) )
                              & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                  & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                | r1_tmap_1(X0,X1,X2,X5) )
                              & X5 = X7
                              & X5 = X6
                              & m1_subset_1(X7,u1_struct_0(X4)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & k1_tsep_1(X0,X3,X4) = X0
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7)
                              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)
                              | ~ r1_tmap_1(X0,X1,sK2,X5) )
                            & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) )
                              | r1_tmap_1(X0,X1,sK2,X5) )
                            & X5 = X7
                            & X5 = X6
                            & m1_subset_1(X7,u1_struct_0(X4)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & k1_tsep_1(X0,X3,X4) = X0
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
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
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)
                                  | ~ r1_tmap_1(X0,sK1,X2,X5) )
                                & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7)
                                    & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) )
                                  | r1_tmap_1(X0,sK1,X2,X5) )
                                & X5 = X7
                                & X5 = X6
                                & m1_subset_1(X7,u1_struct_0(X4)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & k1_tsep_1(X0,X3,X4) = X0
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
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
                                    ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | r1_tmap_1(X0,X1,X2,X5) )
                                    & X5 = X7
                                    & X5 = X6
                                    & m1_subset_1(X7,u1_struct_0(X4)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(sK0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) )
                                    | r1_tmap_1(sK0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & k1_tsep_1(sK0,X3,X4) = sK0
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
      | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
    & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
      | r1_tmap_1(sK0,sK1,sK2,sK5) )
    & sK5 = sK7
    & sK5 = sK6
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & k1_tsep_1(sK0,sK3,sK4) = sK0
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK0) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
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

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f44])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( ( X5 = X7
                                      & X5 = X6 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                    <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f81,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f70,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f83,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_827,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1352,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_376,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_377,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_381,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_28])).

cnf(c_382,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_381])).

cnf(c_817,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X2_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X2_58)
    | u1_struct_0(X1_58) != u1_struct_0(sK0)
    | u1_struct_0(X2_58) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(X2_58),sK2,u1_struct_0(X0_58)) = k2_tmap_1(X1_58,X2_58,sK2,X0_58) ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1362,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK2,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,sK2,X2_58)
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_3513,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1362])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_844,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_1669,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_2062,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X1_58)
    | v2_struct_0(sK1)
    | u1_struct_0(X1_58) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(sK1),sK2,u1_struct_0(X0_58)) = k2_tmap_1(X1_58,sK1,sK2,X0_58) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_2063,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2062])).

cnf(c_3833,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
    | u1_struct_0(X0_58) != u1_struct_0(sK0)
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3513,c_38,c_39,c_40,c_1669,c_2063])).

cnf(c_3834,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_3833])).

cnf(c_3846,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_58)) = k2_tmap_1(sK0,sK1,sK2,X0_58)
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3834])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_825,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1354,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_28])).

cnf(c_623,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK2,X2) = k7_relat_1(sK2,X2) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_813,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k2_partfun1(X0_56,X1_56,sK2,X2_56) = k7_relat_1(sK2,X2_56) ),
    inference(subtyping,[status(esa)],[c_623])).

cnf(c_1366,plain,
    ( k2_partfun1(X0_56,X1_56,sK2,X2_56) = k7_relat_1(sK2,X2_56)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_3129,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k7_relat_1(sK2,X0_56) ),
    inference(superposition,[status(thm)],[c_1354,c_1366])).

cnf(c_3847,plain,
    ( k2_tmap_1(sK0,sK1,sK2,X0_58) = k7_relat_1(sK2,u1_struct_0(X0_58))
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_3129])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3852,plain,
    ( k2_tmap_1(sK0,sK1,sK2,X0_58) = k7_relat_1(sK2,u1_struct_0(X0_58))
    | m1_pre_topc(X0_58,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3847,c_35,c_36,c_37,c_43])).

cnf(c_3861,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1352,c_3852])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_836,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1346,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_16,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_835,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_17,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_834,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1369,plain,
    ( sK6 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_834,c_835])).

cnf(c_1413,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1346,c_835,c_1369])).

cnf(c_3904,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3861,c_1413])).

cnf(c_21,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_830,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
    | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_549,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
    | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_550,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_28])).

cnf(c_555,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_554])).

cnf(c_814,plain,
    ( ~ r1_tmap_1(X0_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X0_58),X0_55)
    | ~ r1_tmap_1(X3_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X3_58),X0_55)
    | r1_tmap_1(k1_tsep_1(X2_58,X0_58,X3_58),X1_58,k2_tmap_1(X2_58,X1_58,sK2,k1_tsep_1(X2_58,X0_58,X3_58)),X0_55)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X2_58,X0_58,X3_58)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | u1_struct_0(X2_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_555])).

cnf(c_1365,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1)
    | r1_tmap_1(X2_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X2_58),X0_55) != iProver_top
    | r1_tmap_1(X3_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X3_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X3_58),X1_58,k2_tmap_1(X0_58,X1_58,sK2,k1_tsep_1(X0_58,X2_58,X3_58)),X0_55) = iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X3_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_3581,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
    | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1365])).

cnf(c_1670,plain,
    ( ~ r1_tmap_1(X0_58,sK1,k2_tmap_1(X1_58,sK1,sK2,X0_58),X0_55)
    | ~ r1_tmap_1(X2_58,sK1,k2_tmap_1(X1_58,sK1,sK2,X2_58),X0_55)
    | r1_tmap_1(k1_tsep_1(X1_58,X0_58,X2_58),sK1,k2_tmap_1(X1_58,sK1,sK2,k1_tsep_1(X1_58,X0_58,X2_58)),X0_55)
    | ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X2_58,X1_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(X2_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X1_58,X0_58,X2_58)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(sK1)
    | u1_struct_0(X1_58) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1679,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
    | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1670])).

cnf(c_5317,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
    | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
    | u1_struct_0(X0_58) != u1_struct_0(sK0)
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3581,c_38,c_39,c_40])).

cnf(c_5318,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
    | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_5317])).

cnf(c_5338,plain,
    ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) != iProver_top
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(sK0,sK1,sK2,X1_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) = iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5318])).

cnf(c_14445,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) != iProver_top
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(sK0,sK1,sK2,X1_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) = iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5338,c_35,c_36,c_37,c_43])).

cnf(c_14446,plain,
    ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) != iProver_top
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(sK0,sK1,sK2,X1_58),X0_55) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) = iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_14445])).

cnf(c_14521,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_55) != iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_55) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_55) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_14446])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_829,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1350,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_3860,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_1350,c_3852])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_840,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X2_58,X1_58)
    | m1_pre_topc(k1_tsep_1(X1_58,X0_58,X2_58),X1_58)
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1342,plain,
    ( m1_pre_topc(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X2_58,X1_58) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_58,X0_58,X2_58),X1_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_2340,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) = iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_1342])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2701,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_35,c_37,c_44,c_45,c_46,c_47])).

cnf(c_3862,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2701,c_3852])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_339,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_3])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_2,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_340,c_2])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_3])).

cnf(c_818,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k7_relat_1(X0_55,X0_56) = X0_55 ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_1361,plain,
    ( k7_relat_1(X0_55,X0_56) = X0_55
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_3665,plain,
    ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_1354,c_1361])).

cnf(c_3879,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3862,c_3665])).

cnf(c_14534,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14521,c_830,c_3860,c_3861,c_3879])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_841,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
    | m1_subset_1(X0_55,u1_struct_0(X1_58))
    | ~ l1_pre_topc(X1_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1736,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | m1_subset_1(X0_55,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1737,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1736])).

cnf(c_16036,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) = iProver_top
    | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14534,c_35,c_37,c_44,c_45,c_46,c_47,c_1737])).

cnf(c_16037,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_16036])).

cnf(c_16047,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_16037])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_421,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_422,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_28])).

cnf(c_427,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_426])).

cnf(c_816,plain,
    ( r1_tmap_1(X0_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X0_58),X0_55)
    | ~ r1_tmap_1(k1_tsep_1(X2_58,X0_58,X3_58),X1_58,k2_tmap_1(X2_58,X1_58,sK2,k1_tsep_1(X2_58,X0_58,X3_58)),X0_55)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X2_58,X0_58,X3_58)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | u1_struct_0(X2_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_1363,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1)
    | r1_tmap_1(X2_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X2_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X3_58),X1_58,k2_tmap_1(X0_58,X1_58,sK2,k1_tsep_1(X0_58,X2_58,X3_58)),X0_55) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X3_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_3536,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1363])).

cnf(c_3948,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) != iProver_top
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
    | u1_struct_0(X0_58) != u1_struct_0(sK0)
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3536,c_38,c_39,c_40,c_1669,c_1677])).

cnf(c_3949,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_3948])).

cnf(c_3968,plain,
    ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3949])).

cnf(c_8404,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3968,c_35,c_36,c_37,c_43])).

cnf(c_8405,plain,
    ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_8404])).

cnf(c_8452,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_55) = iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_55) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_8405])).

cnf(c_8462,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8452,c_830,c_3861,c_3879])).

cnf(c_9162,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
    | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8462,c_35,c_37,c_44,c_45,c_46,c_47,c_1737])).

cnf(c_9163,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9162])).

cnf(c_11,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_487,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v1_funct_1(X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_488,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_490,plain,
    ( v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_28])).

cnf(c_491,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_490])).

cnf(c_815,plain,
    ( r1_tmap_1(X0_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X0_58),X0_55)
    | ~ r1_tmap_1(k1_tsep_1(X2_58,X3_58,X0_58),X1_58,k2_tmap_1(X2_58,X1_58,sK2,k1_tsep_1(X2_58,X3_58,X0_58)),X0_55)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X3_58,X2_58)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(X3_58))
    | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X2_58,X3_58,X0_58)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
    | ~ v2_pre_topc(X1_58)
    | ~ v2_pre_topc(X2_58)
    | ~ l1_pre_topc(X1_58)
    | ~ l1_pre_topc(X2_58)
    | v2_struct_0(X1_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | u1_struct_0(X2_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_491])).

cnf(c_1364,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | u1_struct_0(X1_58) != u1_struct_0(sK1)
    | r1_tmap_1(X2_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X2_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X3_58,X2_58),X1_58,k2_tmap_1(X0_58,X1_58,sK2,k1_tsep_1(X0_58,X3_58,X2_58)),X0_55) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X3_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X3_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X3_58,X2_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_3559,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X1_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X2_58,X1_58)),X0_55) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X1_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1364])).

cnf(c_4615,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X1_58))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X1_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X2_58,X1_58)),X0_55) != iProver_top
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
    | u1_struct_0(X0_58) != u1_struct_0(sK0)
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3559,c_38,c_39,c_40])).

cnf(c_4616,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK0)
    | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X1_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X2_58,X1_58)),X0_55) != iProver_top
    | m1_pre_topc(X2_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X1_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_4615])).

cnf(c_4633,plain,
    ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_58,X0_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_58,X0_58)),X0_55) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X1_58,X0_58))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4616])).

cnf(c_10368,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_58,X0_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_58,X0_58)),X0_55) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X1_58,X0_58))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4633,c_35,c_36,c_37,c_43])).

cnf(c_10369,plain,
    ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_58,X0_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_58,X0_58)),X0_55) != iProver_top
    | m1_pre_topc(X0_58,sK0) != iProver_top
    | m1_pre_topc(X1_58,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X1_58,X0_58))) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top ),
    inference(renaming,[status(thm)],[c_10368])).

cnf(c_10428,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_55) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_55) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_830,c_10369])).

cnf(c_10438,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10428,c_830,c_3860,c_3879])).

cnf(c_11398,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10438,c_35,c_37,c_44,c_45,c_46,c_47,c_1737])).

cnf(c_11399,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11398])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_838,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1344,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_1422,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1344,c_835,c_1369])).

cnf(c_3890,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3860,c_1422])).

cnf(c_3915,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3890,c_3861])).

cnf(c_11408,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11399,c_3915])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_832,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1348,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_1394,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1348,c_1369])).

cnf(c_11612,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11408,c_50,c_1394])).

cnf(c_11619,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9163,c_11612])).

cnf(c_14,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_837,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1345,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_1408,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1345,c_835])).

cnf(c_3889,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3860,c_1408])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16047,c_11619,c_3889,c_1394,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.34/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/1.50  
% 6.34/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.34/1.50  
% 6.34/1.50  ------  iProver source info
% 6.34/1.50  
% 6.34/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.34/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.34/1.50  git: non_committed_changes: false
% 6.34/1.50  git: last_make_outside_of_git: false
% 6.34/1.50  
% 6.34/1.50  ------ 
% 6.34/1.50  
% 6.34/1.50  ------ Input Options
% 6.34/1.50  
% 6.34/1.50  --out_options                           all
% 6.34/1.50  --tptp_safe_out                         true
% 6.34/1.50  --problem_path                          ""
% 6.34/1.50  --include_path                          ""
% 6.34/1.50  --clausifier                            res/vclausify_rel
% 6.34/1.50  --clausifier_options                    --mode clausify
% 6.34/1.50  --stdin                                 false
% 6.34/1.50  --stats_out                             all
% 6.34/1.50  
% 6.34/1.50  ------ General Options
% 6.34/1.50  
% 6.34/1.50  --fof                                   false
% 6.34/1.50  --time_out_real                         305.
% 6.34/1.50  --time_out_virtual                      -1.
% 6.34/1.50  --symbol_type_check                     false
% 6.34/1.50  --clausify_out                          false
% 6.34/1.50  --sig_cnt_out                           false
% 6.34/1.50  --trig_cnt_out                          false
% 6.34/1.50  --trig_cnt_out_tolerance                1.
% 6.34/1.50  --trig_cnt_out_sk_spl                   false
% 6.34/1.50  --abstr_cl_out                          false
% 6.34/1.50  
% 6.34/1.50  ------ Global Options
% 6.34/1.50  
% 6.34/1.50  --schedule                              default
% 6.34/1.50  --add_important_lit                     false
% 6.34/1.50  --prop_solver_per_cl                    1000
% 6.34/1.50  --min_unsat_core                        false
% 6.34/1.50  --soft_assumptions                      false
% 6.34/1.50  --soft_lemma_size                       3
% 6.34/1.50  --prop_impl_unit_size                   0
% 6.34/1.50  --prop_impl_unit                        []
% 6.34/1.50  --share_sel_clauses                     true
% 6.34/1.50  --reset_solvers                         false
% 6.34/1.50  --bc_imp_inh                            [conj_cone]
% 6.34/1.50  --conj_cone_tolerance                   3.
% 6.34/1.50  --extra_neg_conj                        none
% 6.34/1.50  --large_theory_mode                     true
% 6.34/1.50  --prolific_symb_bound                   200
% 6.34/1.50  --lt_threshold                          2000
% 6.34/1.50  --clause_weak_htbl                      true
% 6.34/1.50  --gc_record_bc_elim                     false
% 6.34/1.50  
% 6.34/1.50  ------ Preprocessing Options
% 6.34/1.50  
% 6.34/1.50  --preprocessing_flag                    true
% 6.34/1.50  --time_out_prep_mult                    0.1
% 6.34/1.50  --splitting_mode                        input
% 6.34/1.50  --splitting_grd                         true
% 6.34/1.50  --splitting_cvd                         false
% 6.34/1.50  --splitting_cvd_svl                     false
% 6.34/1.50  --splitting_nvd                         32
% 6.34/1.50  --sub_typing                            true
% 6.34/1.50  --prep_gs_sim                           true
% 6.34/1.50  --prep_unflatten                        true
% 6.34/1.50  --prep_res_sim                          true
% 6.34/1.50  --prep_upred                            true
% 6.34/1.50  --prep_sem_filter                       exhaustive
% 6.34/1.50  --prep_sem_filter_out                   false
% 6.34/1.50  --pred_elim                             true
% 6.34/1.50  --res_sim_input                         true
% 6.34/1.50  --eq_ax_congr_red                       true
% 6.34/1.50  --pure_diseq_elim                       true
% 6.34/1.50  --brand_transform                       false
% 6.34/1.50  --non_eq_to_eq                          false
% 6.34/1.50  --prep_def_merge                        true
% 6.34/1.50  --prep_def_merge_prop_impl              false
% 6.34/1.50  --prep_def_merge_mbd                    true
% 6.34/1.50  --prep_def_merge_tr_red                 false
% 6.34/1.50  --prep_def_merge_tr_cl                  false
% 6.34/1.50  --smt_preprocessing                     true
% 6.34/1.50  --smt_ac_axioms                         fast
% 6.34/1.50  --preprocessed_out                      false
% 6.34/1.50  --preprocessed_stats                    false
% 6.34/1.50  
% 6.34/1.50  ------ Abstraction refinement Options
% 6.34/1.50  
% 6.34/1.50  --abstr_ref                             []
% 6.34/1.50  --abstr_ref_prep                        false
% 6.34/1.50  --abstr_ref_until_sat                   false
% 6.34/1.50  --abstr_ref_sig_restrict                funpre
% 6.34/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.34/1.50  --abstr_ref_under                       []
% 6.34/1.50  
% 6.34/1.50  ------ SAT Options
% 6.34/1.50  
% 6.34/1.50  --sat_mode                              false
% 6.34/1.50  --sat_fm_restart_options                ""
% 6.34/1.50  --sat_gr_def                            false
% 6.34/1.50  --sat_epr_types                         true
% 6.34/1.50  --sat_non_cyclic_types                  false
% 6.34/1.50  --sat_finite_models                     false
% 6.34/1.50  --sat_fm_lemmas                         false
% 6.34/1.50  --sat_fm_prep                           false
% 6.34/1.50  --sat_fm_uc_incr                        true
% 6.34/1.50  --sat_out_model                         small
% 6.34/1.50  --sat_out_clauses                       false
% 6.34/1.50  
% 6.34/1.50  ------ QBF Options
% 6.34/1.50  
% 6.34/1.50  --qbf_mode                              false
% 6.34/1.50  --qbf_elim_univ                         false
% 6.34/1.50  --qbf_dom_inst                          none
% 6.34/1.50  --qbf_dom_pre_inst                      false
% 6.34/1.50  --qbf_sk_in                             false
% 6.34/1.50  --qbf_pred_elim                         true
% 6.34/1.50  --qbf_split                             512
% 6.34/1.50  
% 6.34/1.50  ------ BMC1 Options
% 6.34/1.50  
% 6.34/1.50  --bmc1_incremental                      false
% 6.34/1.50  --bmc1_axioms                           reachable_all
% 6.34/1.50  --bmc1_min_bound                        0
% 6.34/1.50  --bmc1_max_bound                        -1
% 6.34/1.50  --bmc1_max_bound_default                -1
% 6.34/1.50  --bmc1_symbol_reachability              true
% 6.34/1.50  --bmc1_property_lemmas                  false
% 6.34/1.50  --bmc1_k_induction                      false
% 6.34/1.50  --bmc1_non_equiv_states                 false
% 6.34/1.50  --bmc1_deadlock                         false
% 6.34/1.50  --bmc1_ucm                              false
% 6.34/1.50  --bmc1_add_unsat_core                   none
% 6.34/1.50  --bmc1_unsat_core_children              false
% 6.34/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.34/1.50  --bmc1_out_stat                         full
% 6.34/1.50  --bmc1_ground_init                      false
% 6.34/1.50  --bmc1_pre_inst_next_state              false
% 6.34/1.50  --bmc1_pre_inst_state                   false
% 6.34/1.50  --bmc1_pre_inst_reach_state             false
% 6.34/1.50  --bmc1_out_unsat_core                   false
% 6.34/1.50  --bmc1_aig_witness_out                  false
% 6.34/1.50  --bmc1_verbose                          false
% 6.34/1.50  --bmc1_dump_clauses_tptp                false
% 6.34/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.34/1.50  --bmc1_dump_file                        -
% 6.34/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.34/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.34/1.50  --bmc1_ucm_extend_mode                  1
% 6.34/1.50  --bmc1_ucm_init_mode                    2
% 6.34/1.50  --bmc1_ucm_cone_mode                    none
% 6.34/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.34/1.50  --bmc1_ucm_relax_model                  4
% 6.34/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.34/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.34/1.50  --bmc1_ucm_layered_model                none
% 6.34/1.50  --bmc1_ucm_max_lemma_size               10
% 6.34/1.50  
% 6.34/1.50  ------ AIG Options
% 6.34/1.50  
% 6.34/1.50  --aig_mode                              false
% 6.34/1.50  
% 6.34/1.50  ------ Instantiation Options
% 6.34/1.50  
% 6.34/1.50  --instantiation_flag                    true
% 6.34/1.50  --inst_sos_flag                         false
% 6.34/1.50  --inst_sos_phase                        true
% 6.34/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.34/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.34/1.50  --inst_lit_sel_side                     num_symb
% 6.34/1.50  --inst_solver_per_active                1400
% 6.34/1.50  --inst_solver_calls_frac                1.
% 6.34/1.50  --inst_passive_queue_type               priority_queues
% 6.34/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.34/1.50  --inst_passive_queues_freq              [25;2]
% 6.34/1.50  --inst_dismatching                      true
% 6.34/1.50  --inst_eager_unprocessed_to_passive     true
% 6.34/1.50  --inst_prop_sim_given                   true
% 6.34/1.50  --inst_prop_sim_new                     false
% 6.34/1.50  --inst_subs_new                         false
% 6.34/1.50  --inst_eq_res_simp                      false
% 6.34/1.50  --inst_subs_given                       false
% 6.34/1.50  --inst_orphan_elimination               true
% 6.34/1.50  --inst_learning_loop_flag               true
% 6.34/1.50  --inst_learning_start                   3000
% 6.34/1.50  --inst_learning_factor                  2
% 6.34/1.50  --inst_start_prop_sim_after_learn       3
% 6.34/1.50  --inst_sel_renew                        solver
% 6.34/1.50  --inst_lit_activity_flag                true
% 6.34/1.50  --inst_restr_to_given                   false
% 6.34/1.50  --inst_activity_threshold               500
% 6.34/1.50  --inst_out_proof                        true
% 6.34/1.50  
% 6.34/1.50  ------ Resolution Options
% 6.34/1.50  
% 6.34/1.50  --resolution_flag                       true
% 6.34/1.50  --res_lit_sel                           adaptive
% 6.34/1.50  --res_lit_sel_side                      none
% 6.34/1.50  --res_ordering                          kbo
% 6.34/1.50  --res_to_prop_solver                    active
% 6.34/1.50  --res_prop_simpl_new                    false
% 6.34/1.50  --res_prop_simpl_given                  true
% 6.34/1.50  --res_passive_queue_type                priority_queues
% 6.34/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.34/1.50  --res_passive_queues_freq               [15;5]
% 6.34/1.50  --res_forward_subs                      full
% 6.34/1.50  --res_backward_subs                     full
% 6.34/1.50  --res_forward_subs_resolution           true
% 6.34/1.50  --res_backward_subs_resolution          true
% 6.34/1.50  --res_orphan_elimination                true
% 6.34/1.50  --res_time_limit                        2.
% 6.34/1.50  --res_out_proof                         true
% 6.34/1.50  
% 6.34/1.50  ------ Superposition Options
% 6.34/1.50  
% 6.34/1.50  --superposition_flag                    true
% 6.34/1.50  --sup_passive_queue_type                priority_queues
% 6.34/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.34/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.34/1.50  --demod_completeness_check              fast
% 6.34/1.50  --demod_use_ground                      true
% 6.34/1.50  --sup_to_prop_solver                    passive
% 6.34/1.50  --sup_prop_simpl_new                    true
% 6.34/1.50  --sup_prop_simpl_given                  true
% 6.34/1.50  --sup_fun_splitting                     false
% 6.34/1.50  --sup_smt_interval                      50000
% 6.34/1.50  
% 6.34/1.50  ------ Superposition Simplification Setup
% 6.34/1.50  
% 6.34/1.50  --sup_indices_passive                   []
% 6.34/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.34/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.50  --sup_full_bw                           [BwDemod]
% 6.34/1.50  --sup_immed_triv                        [TrivRules]
% 6.34/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.34/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.50  --sup_immed_bw_main                     []
% 6.34/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.34/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.50  
% 6.34/1.50  ------ Combination Options
% 6.34/1.50  
% 6.34/1.50  --comb_res_mult                         3
% 6.34/1.50  --comb_sup_mult                         2
% 6.34/1.50  --comb_inst_mult                        10
% 6.34/1.50  
% 6.34/1.50  ------ Debug Options
% 6.34/1.50  
% 6.34/1.50  --dbg_backtrace                         false
% 6.34/1.50  --dbg_dump_prop_clauses                 false
% 6.34/1.50  --dbg_dump_prop_clauses_file            -
% 6.34/1.50  --dbg_out_stat                          false
% 6.34/1.50  ------ Parsing...
% 6.34/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.34/1.50  
% 6.34/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.34/1.50  
% 6.34/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.34/1.50  
% 6.34/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.34/1.50  ------ Proving...
% 6.34/1.50  ------ Problem Properties 
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  clauses                                 29
% 6.34/1.50  conjectures                             20
% 6.34/1.50  EPR                                     12
% 6.34/1.50  Horn                                    20
% 6.34/1.50  unary                                   17
% 6.34/1.50  binary                                  4
% 6.34/1.50  lits                                    114
% 6.34/1.50  lits eq                                 14
% 6.34/1.50  fd_pure                                 0
% 6.34/1.50  fd_pseudo                               0
% 6.34/1.50  fd_cond                                 0
% 6.34/1.50  fd_pseudo_cond                          0
% 6.34/1.50  AC symbols                              0
% 6.34/1.50  
% 6.34/1.50  ------ Schedule dynamic 5 is on 
% 6.34/1.50  
% 6.34/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  ------ 
% 6.34/1.50  Current options:
% 6.34/1.50  ------ 
% 6.34/1.50  
% 6.34/1.50  ------ Input Options
% 6.34/1.50  
% 6.34/1.50  --out_options                           all
% 6.34/1.50  --tptp_safe_out                         true
% 6.34/1.50  --problem_path                          ""
% 6.34/1.50  --include_path                          ""
% 6.34/1.50  --clausifier                            res/vclausify_rel
% 6.34/1.50  --clausifier_options                    --mode clausify
% 6.34/1.50  --stdin                                 false
% 6.34/1.50  --stats_out                             all
% 6.34/1.50  
% 6.34/1.50  ------ General Options
% 6.34/1.50  
% 6.34/1.50  --fof                                   false
% 6.34/1.50  --time_out_real                         305.
% 6.34/1.50  --time_out_virtual                      -1.
% 6.34/1.50  --symbol_type_check                     false
% 6.34/1.50  --clausify_out                          false
% 6.34/1.50  --sig_cnt_out                           false
% 6.34/1.50  --trig_cnt_out                          false
% 6.34/1.50  --trig_cnt_out_tolerance                1.
% 6.34/1.50  --trig_cnt_out_sk_spl                   false
% 6.34/1.50  --abstr_cl_out                          false
% 6.34/1.50  
% 6.34/1.50  ------ Global Options
% 6.34/1.50  
% 6.34/1.50  --schedule                              default
% 6.34/1.50  --add_important_lit                     false
% 6.34/1.50  --prop_solver_per_cl                    1000
% 6.34/1.50  --min_unsat_core                        false
% 6.34/1.50  --soft_assumptions                      false
% 6.34/1.50  --soft_lemma_size                       3
% 6.34/1.50  --prop_impl_unit_size                   0
% 6.34/1.50  --prop_impl_unit                        []
% 6.34/1.50  --share_sel_clauses                     true
% 6.34/1.50  --reset_solvers                         false
% 6.34/1.50  --bc_imp_inh                            [conj_cone]
% 6.34/1.50  --conj_cone_tolerance                   3.
% 6.34/1.50  --extra_neg_conj                        none
% 6.34/1.50  --large_theory_mode                     true
% 6.34/1.50  --prolific_symb_bound                   200
% 6.34/1.50  --lt_threshold                          2000
% 6.34/1.50  --clause_weak_htbl                      true
% 6.34/1.50  --gc_record_bc_elim                     false
% 6.34/1.50  
% 6.34/1.50  ------ Preprocessing Options
% 6.34/1.50  
% 6.34/1.50  --preprocessing_flag                    true
% 6.34/1.50  --time_out_prep_mult                    0.1
% 6.34/1.50  --splitting_mode                        input
% 6.34/1.50  --splitting_grd                         true
% 6.34/1.50  --splitting_cvd                         false
% 6.34/1.50  --splitting_cvd_svl                     false
% 6.34/1.50  --splitting_nvd                         32
% 6.34/1.50  --sub_typing                            true
% 6.34/1.50  --prep_gs_sim                           true
% 6.34/1.50  --prep_unflatten                        true
% 6.34/1.50  --prep_res_sim                          true
% 6.34/1.50  --prep_upred                            true
% 6.34/1.50  --prep_sem_filter                       exhaustive
% 6.34/1.50  --prep_sem_filter_out                   false
% 6.34/1.50  --pred_elim                             true
% 6.34/1.50  --res_sim_input                         true
% 6.34/1.50  --eq_ax_congr_red                       true
% 6.34/1.50  --pure_diseq_elim                       true
% 6.34/1.50  --brand_transform                       false
% 6.34/1.50  --non_eq_to_eq                          false
% 6.34/1.50  --prep_def_merge                        true
% 6.34/1.50  --prep_def_merge_prop_impl              false
% 6.34/1.50  --prep_def_merge_mbd                    true
% 6.34/1.50  --prep_def_merge_tr_red                 false
% 6.34/1.50  --prep_def_merge_tr_cl                  false
% 6.34/1.50  --smt_preprocessing                     true
% 6.34/1.50  --smt_ac_axioms                         fast
% 6.34/1.50  --preprocessed_out                      false
% 6.34/1.50  --preprocessed_stats                    false
% 6.34/1.50  
% 6.34/1.50  ------ Abstraction refinement Options
% 6.34/1.50  
% 6.34/1.50  --abstr_ref                             []
% 6.34/1.50  --abstr_ref_prep                        false
% 6.34/1.50  --abstr_ref_until_sat                   false
% 6.34/1.50  --abstr_ref_sig_restrict                funpre
% 6.34/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.34/1.50  --abstr_ref_under                       []
% 6.34/1.50  
% 6.34/1.50  ------ SAT Options
% 6.34/1.50  
% 6.34/1.50  --sat_mode                              false
% 6.34/1.50  --sat_fm_restart_options                ""
% 6.34/1.50  --sat_gr_def                            false
% 6.34/1.50  --sat_epr_types                         true
% 6.34/1.50  --sat_non_cyclic_types                  false
% 6.34/1.50  --sat_finite_models                     false
% 6.34/1.50  --sat_fm_lemmas                         false
% 6.34/1.50  --sat_fm_prep                           false
% 6.34/1.50  --sat_fm_uc_incr                        true
% 6.34/1.50  --sat_out_model                         small
% 6.34/1.50  --sat_out_clauses                       false
% 6.34/1.50  
% 6.34/1.50  ------ QBF Options
% 6.34/1.50  
% 6.34/1.50  --qbf_mode                              false
% 6.34/1.50  --qbf_elim_univ                         false
% 6.34/1.50  --qbf_dom_inst                          none
% 6.34/1.50  --qbf_dom_pre_inst                      false
% 6.34/1.50  --qbf_sk_in                             false
% 6.34/1.50  --qbf_pred_elim                         true
% 6.34/1.50  --qbf_split                             512
% 6.34/1.50  
% 6.34/1.50  ------ BMC1 Options
% 6.34/1.50  
% 6.34/1.50  --bmc1_incremental                      false
% 6.34/1.50  --bmc1_axioms                           reachable_all
% 6.34/1.50  --bmc1_min_bound                        0
% 6.34/1.50  --bmc1_max_bound                        -1
% 6.34/1.50  --bmc1_max_bound_default                -1
% 6.34/1.50  --bmc1_symbol_reachability              true
% 6.34/1.50  --bmc1_property_lemmas                  false
% 6.34/1.50  --bmc1_k_induction                      false
% 6.34/1.50  --bmc1_non_equiv_states                 false
% 6.34/1.50  --bmc1_deadlock                         false
% 6.34/1.50  --bmc1_ucm                              false
% 6.34/1.50  --bmc1_add_unsat_core                   none
% 6.34/1.50  --bmc1_unsat_core_children              false
% 6.34/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.34/1.50  --bmc1_out_stat                         full
% 6.34/1.50  --bmc1_ground_init                      false
% 6.34/1.50  --bmc1_pre_inst_next_state              false
% 6.34/1.50  --bmc1_pre_inst_state                   false
% 6.34/1.50  --bmc1_pre_inst_reach_state             false
% 6.34/1.50  --bmc1_out_unsat_core                   false
% 6.34/1.50  --bmc1_aig_witness_out                  false
% 6.34/1.50  --bmc1_verbose                          false
% 6.34/1.50  --bmc1_dump_clauses_tptp                false
% 6.34/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.34/1.50  --bmc1_dump_file                        -
% 6.34/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.34/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.34/1.50  --bmc1_ucm_extend_mode                  1
% 6.34/1.50  --bmc1_ucm_init_mode                    2
% 6.34/1.50  --bmc1_ucm_cone_mode                    none
% 6.34/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.34/1.50  --bmc1_ucm_relax_model                  4
% 6.34/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.34/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.34/1.50  --bmc1_ucm_layered_model                none
% 6.34/1.50  --bmc1_ucm_max_lemma_size               10
% 6.34/1.50  
% 6.34/1.50  ------ AIG Options
% 6.34/1.50  
% 6.34/1.50  --aig_mode                              false
% 6.34/1.50  
% 6.34/1.50  ------ Instantiation Options
% 6.34/1.50  
% 6.34/1.50  --instantiation_flag                    true
% 6.34/1.50  --inst_sos_flag                         false
% 6.34/1.50  --inst_sos_phase                        true
% 6.34/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.34/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.34/1.50  --inst_lit_sel_side                     none
% 6.34/1.50  --inst_solver_per_active                1400
% 6.34/1.50  --inst_solver_calls_frac                1.
% 6.34/1.50  --inst_passive_queue_type               priority_queues
% 6.34/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.34/1.50  --inst_passive_queues_freq              [25;2]
% 6.34/1.50  --inst_dismatching                      true
% 6.34/1.50  --inst_eager_unprocessed_to_passive     true
% 6.34/1.50  --inst_prop_sim_given                   true
% 6.34/1.50  --inst_prop_sim_new                     false
% 6.34/1.50  --inst_subs_new                         false
% 6.34/1.50  --inst_eq_res_simp                      false
% 6.34/1.50  --inst_subs_given                       false
% 6.34/1.50  --inst_orphan_elimination               true
% 6.34/1.50  --inst_learning_loop_flag               true
% 6.34/1.50  --inst_learning_start                   3000
% 6.34/1.50  --inst_learning_factor                  2
% 6.34/1.50  --inst_start_prop_sim_after_learn       3
% 6.34/1.50  --inst_sel_renew                        solver
% 6.34/1.50  --inst_lit_activity_flag                true
% 6.34/1.50  --inst_restr_to_given                   false
% 6.34/1.50  --inst_activity_threshold               500
% 6.34/1.50  --inst_out_proof                        true
% 6.34/1.50  
% 6.34/1.50  ------ Resolution Options
% 6.34/1.50  
% 6.34/1.50  --resolution_flag                       false
% 6.34/1.50  --res_lit_sel                           adaptive
% 6.34/1.50  --res_lit_sel_side                      none
% 6.34/1.50  --res_ordering                          kbo
% 6.34/1.50  --res_to_prop_solver                    active
% 6.34/1.50  --res_prop_simpl_new                    false
% 6.34/1.50  --res_prop_simpl_given                  true
% 6.34/1.50  --res_passive_queue_type                priority_queues
% 6.34/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.34/1.50  --res_passive_queues_freq               [15;5]
% 6.34/1.50  --res_forward_subs                      full
% 6.34/1.50  --res_backward_subs                     full
% 6.34/1.50  --res_forward_subs_resolution           true
% 6.34/1.50  --res_backward_subs_resolution          true
% 6.34/1.50  --res_orphan_elimination                true
% 6.34/1.50  --res_time_limit                        2.
% 6.34/1.50  --res_out_proof                         true
% 6.34/1.50  
% 6.34/1.50  ------ Superposition Options
% 6.34/1.50  
% 6.34/1.50  --superposition_flag                    true
% 6.34/1.50  --sup_passive_queue_type                priority_queues
% 6.34/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.34/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.34/1.50  --demod_completeness_check              fast
% 6.34/1.50  --demod_use_ground                      true
% 6.34/1.50  --sup_to_prop_solver                    passive
% 6.34/1.50  --sup_prop_simpl_new                    true
% 6.34/1.50  --sup_prop_simpl_given                  true
% 6.34/1.50  --sup_fun_splitting                     false
% 6.34/1.50  --sup_smt_interval                      50000
% 6.34/1.50  
% 6.34/1.50  ------ Superposition Simplification Setup
% 6.34/1.50  
% 6.34/1.50  --sup_indices_passive                   []
% 6.34/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.34/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.50  --sup_full_bw                           [BwDemod]
% 6.34/1.50  --sup_immed_triv                        [TrivRules]
% 6.34/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.34/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.50  --sup_immed_bw_main                     []
% 6.34/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.34/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.50  
% 6.34/1.50  ------ Combination Options
% 6.34/1.50  
% 6.34/1.50  --comb_res_mult                         3
% 6.34/1.50  --comb_sup_mult                         2
% 6.34/1.50  --comb_inst_mult                        10
% 6.34/1.50  
% 6.34/1.50  ------ Debug Options
% 6.34/1.50  
% 6.34/1.50  --dbg_backtrace                         false
% 6.34/1.50  --dbg_dump_prop_clauses                 false
% 6.34/1.50  --dbg_dump_prop_clauses_file            -
% 6.34/1.50  --dbg_out_stat                          false
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  ------ Proving...
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  % SZS status Theorem for theBenchmark.p
% 6.34/1.50  
% 6.34/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.34/1.50  
% 6.34/1.50  fof(f10,conjecture,(
% 6.34/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f11,negated_conjecture,(
% 6.34/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 6.34/1.50    inference(negated_conjecture,[],[f10])).
% 6.34/1.50  
% 6.34/1.50  fof(f29,plain,(
% 6.34/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 6.34/1.50    inference(ennf_transformation,[],[f11])).
% 6.34/1.50  
% 6.34/1.50  fof(f30,plain,(
% 6.34/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f29])).
% 6.34/1.50  
% 6.34/1.50  fof(f34,plain,(
% 6.34/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.34/1.50    inference(nnf_transformation,[],[f30])).
% 6.34/1.50  
% 6.34/1.50  fof(f35,plain,(
% 6.34/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f34])).
% 6.34/1.50  
% 6.34/1.50  fof(f43,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK7 = X5 & X5 = X6 & m1_subset_1(sK7,u1_struct_0(X4)))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f42,plain,(
% 6.34/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK6 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f41,plain,(
% 6.34/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f40,plain,(
% 6.34/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK4) = X0 & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f39,plain,(
% 6.34/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f38,plain,(
% 6.34/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) | ~r1_tmap_1(X0,X1,sK2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)) | r1_tmap_1(X0,X1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f37,plain,(
% 6.34/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) | ~r1_tmap_1(X0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)) | r1_tmap_1(X0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f36,plain,(
% 6.34/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & k1_tsep_1(sK0,X3,X4) = sK0 & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 6.34/1.50    introduced(choice_axiom,[])).
% 6.34/1.50  
% 6.34/1.50  fof(f44,plain,(
% 6.34/1.50    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & k1_tsep_1(sK0,sK3,sK4) = sK0 & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 6.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f35,f43,f42,f41,f40,f39,f38,f37,f36])).
% 6.34/1.50  
% 6.34/1.50  fof(f68,plain,(
% 6.34/1.50    m1_pre_topc(sK3,sK0)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f7,axiom,(
% 6.34/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f23,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.34/1.50    inference(ennf_transformation,[],[f7])).
% 6.34/1.50  
% 6.34/1.50  fof(f24,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f23])).
% 6.34/1.50  
% 6.34/1.50  fof(f52,plain,(
% 6.34/1.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f24])).
% 6.34/1.50  
% 6.34/1.50  fof(f65,plain,(
% 6.34/1.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f64,plain,(
% 6.34/1.50    v1_funct_1(sK2)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f61,plain,(
% 6.34/1.50    ~v2_struct_0(sK1)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f62,plain,(
% 6.34/1.50    v2_pre_topc(sK1)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f63,plain,(
% 6.34/1.50    l1_pre_topc(sK1)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f66,plain,(
% 6.34/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f5,axiom,(
% 6.34/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f19,plain,(
% 6.34/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.34/1.50    inference(ennf_transformation,[],[f5])).
% 6.34/1.50  
% 6.34/1.50  fof(f20,plain,(
% 6.34/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.34/1.50    inference(flattening,[],[f19])).
% 6.34/1.50  
% 6.34/1.50  fof(f50,plain,(
% 6.34/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f20])).
% 6.34/1.50  
% 6.34/1.50  fof(f58,plain,(
% 6.34/1.50    ~v2_struct_0(sK0)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f59,plain,(
% 6.34/1.50    v2_pre_topc(sK0)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f60,plain,(
% 6.34/1.50    l1_pre_topc(sK0)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f77,plain,(
% 6.34/1.50    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f76,plain,(
% 6.34/1.50    sK5 = sK7),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f75,plain,(
% 6.34/1.50    sK5 = sK6),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f71,plain,(
% 6.34/1.50    k1_tsep_1(sK0,sK3,sK4) = sK0),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f9,axiom,(
% 6.34/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f27,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.34/1.50    inference(ennf_transformation,[],[f9])).
% 6.34/1.50  
% 6.34/1.50  fof(f28,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f27])).
% 6.34/1.50  
% 6.34/1.50  fof(f32,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.34/1.50    inference(nnf_transformation,[],[f28])).
% 6.34/1.50  
% 6.34/1.50  fof(f33,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f32])).
% 6.34/1.50  
% 6.34/1.50  fof(f57,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f33])).
% 6.34/1.50  
% 6.34/1.50  fof(f80,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(equality_resolution,[],[f57])).
% 6.34/1.50  
% 6.34/1.50  fof(f81,plain,(
% 6.34/1.50    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(equality_resolution,[],[f80])).
% 6.34/1.50  
% 6.34/1.50  fof(f70,plain,(
% 6.34/1.50    m1_pre_topc(sK4,sK0)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f8,axiom,(
% 6.34/1.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f12,plain,(
% 6.34/1.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 6.34/1.50    inference(pure_predicate_removal,[],[f8])).
% 6.34/1.50  
% 6.34/1.50  fof(f25,plain,(
% 6.34/1.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 6.34/1.50    inference(ennf_transformation,[],[f12])).
% 6.34/1.50  
% 6.34/1.50  fof(f26,plain,(
% 6.34/1.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f25])).
% 6.34/1.50  
% 6.34/1.50  fof(f54,plain,(
% 6.34/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f26])).
% 6.34/1.50  
% 6.34/1.50  fof(f67,plain,(
% 6.34/1.50    ~v2_struct_0(sK3)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f69,plain,(
% 6.34/1.50    ~v2_struct_0(sK4)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f4,axiom,(
% 6.34/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f13,plain,(
% 6.34/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.34/1.50    inference(pure_predicate_removal,[],[f4])).
% 6.34/1.50  
% 6.34/1.50  fof(f18,plain,(
% 6.34/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.50    inference(ennf_transformation,[],[f13])).
% 6.34/1.50  
% 6.34/1.50  fof(f49,plain,(
% 6.34/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.34/1.50    inference(cnf_transformation,[],[f18])).
% 6.34/1.50  
% 6.34/1.50  fof(f1,axiom,(
% 6.34/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f14,plain,(
% 6.34/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.34/1.50    inference(ennf_transformation,[],[f1])).
% 6.34/1.50  
% 6.34/1.50  fof(f31,plain,(
% 6.34/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.34/1.50    inference(nnf_transformation,[],[f14])).
% 6.34/1.50  
% 6.34/1.50  fof(f45,plain,(
% 6.34/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f31])).
% 6.34/1.50  
% 6.34/1.50  fof(f3,axiom,(
% 6.34/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f17,plain,(
% 6.34/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.50    inference(ennf_transformation,[],[f3])).
% 6.34/1.50  
% 6.34/1.50  fof(f48,plain,(
% 6.34/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.34/1.50    inference(cnf_transformation,[],[f17])).
% 6.34/1.50  
% 6.34/1.50  fof(f2,axiom,(
% 6.34/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f15,plain,(
% 6.34/1.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.34/1.50    inference(ennf_transformation,[],[f2])).
% 6.34/1.50  
% 6.34/1.50  fof(f16,plain,(
% 6.34/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.34/1.50    inference(flattening,[],[f15])).
% 6.34/1.50  
% 6.34/1.50  fof(f47,plain,(
% 6.34/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f16])).
% 6.34/1.50  
% 6.34/1.50  fof(f6,axiom,(
% 6.34/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 6.34/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.34/1.50  
% 6.34/1.50  fof(f21,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 6.34/1.50    inference(ennf_transformation,[],[f6])).
% 6.34/1.50  
% 6.34/1.50  fof(f22,plain,(
% 6.34/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.34/1.50    inference(flattening,[],[f21])).
% 6.34/1.50  
% 6.34/1.50  fof(f51,plain,(
% 6.34/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f22])).
% 6.34/1.50  
% 6.34/1.50  fof(f55,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f33])).
% 6.34/1.50  
% 6.34/1.50  fof(f84,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(equality_resolution,[],[f55])).
% 6.34/1.50  
% 6.34/1.50  fof(f85,plain,(
% 6.34/1.50    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(equality_resolution,[],[f84])).
% 6.34/1.50  
% 6.34/1.50  fof(f56,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(cnf_transformation,[],[f33])).
% 6.34/1.50  
% 6.34/1.50  fof(f82,plain,(
% 6.34/1.50    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(equality_resolution,[],[f56])).
% 6.34/1.50  
% 6.34/1.50  fof(f83,plain,(
% 6.34/1.50    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.34/1.50    inference(equality_resolution,[],[f82])).
% 6.34/1.50  
% 6.34/1.50  fof(f79,plain,(
% 6.34/1.50    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f74,plain,(
% 6.34/1.50    m1_subset_1(sK7,u1_struct_0(sK4))),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f73,plain,(
% 6.34/1.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  fof(f78,plain,(
% 6.34/1.50    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 6.34/1.50    inference(cnf_transformation,[],[f44])).
% 6.34/1.50  
% 6.34/1.50  cnf(c_24,negated_conjecture,
% 6.34/1.50      ( m1_pre_topc(sK3,sK0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f68]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_827,negated_conjecture,
% 6.34/1.50      ( m1_pre_topc(sK3,sK0) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1352,plain,
% 6.34/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_7,plain,
% 6.34/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.34/1.50      | ~ m1_pre_topc(X3,X1)
% 6.34/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | ~ v1_funct_1(X0)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 6.34/1.50      inference(cnf_transformation,[],[f52]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_27,negated_conjecture,
% 6.34/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 6.34/1.50      inference(cnf_transformation,[],[f65]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_376,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0,X1)
% 6.34/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X3)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X3)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X3)
% 6.34/1.50      | ~ v1_funct_1(X2)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X3) != u1_struct_0(sK1)
% 6.34/1.50      | sK2 != X2 ),
% 6.34/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_377,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0,X1)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | ~ v1_funct_1(sK2)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(unflattening,[status(thm)],[c_376]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_28,negated_conjecture,
% 6.34/1.50      ( v1_funct_1(sK2) ),
% 6.34/1.50      inference(cnf_transformation,[],[f64]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_381,plain,
% 6.34/1.50      ( v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.34/1.50      | ~ m1_pre_topc(X0,X1)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_377,c_28]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_382,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0,X1)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_381]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_817,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0_58,X1_58)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X2_58))))
% 6.34/1.50      | ~ v2_pre_topc(X1_58)
% 6.34/1.50      | ~ v2_pre_topc(X2_58)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | ~ l1_pre_topc(X2_58)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X2_58)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X2_58) != u1_struct_0(sK1)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(X2_58),sK2,u1_struct_0(X0_58)) = k2_tmap_1(X1_58,X2_58,sK2,X0_58) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_382]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1362,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(X1_58),sK2,u1_struct_0(X2_58)) = k2_tmap_1(X0_58,X1_58,sK2,X2_58)
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3513,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK1) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK1) != iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK1) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_1362]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_31,negated_conjecture,
% 6.34/1.50      ( ~ v2_struct_0(sK1) ),
% 6.34/1.50      inference(cnf_transformation,[],[f61]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_38,plain,
% 6.34/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_30,negated_conjecture,
% 6.34/1.50      ( v2_pre_topc(sK1) ),
% 6.34/1.50      inference(cnf_transformation,[],[f62]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_39,plain,
% 6.34/1.50      ( v2_pre_topc(sK1) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_29,negated_conjecture,
% 6.34/1.50      ( l1_pre_topc(sK1) ),
% 6.34/1.50      inference(cnf_transformation,[],[f63]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_40,plain,
% 6.34/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_844,plain,( X0_56 = X0_56 ),theory(equality) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1669,plain,
% 6.34/1.50      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 6.34/1.50      inference(instantiation,[status(thm)],[c_844]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_2062,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0_58,X1_58)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK1))))
% 6.34/1.50      | ~ v2_pre_topc(X1_58)
% 6.34/1.50      | ~ v2_pre_topc(sK1)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | ~ l1_pre_topc(sK1)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(sK1)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(sK1),sK2,u1_struct_0(X0_58)) = k2_tmap_1(X1_58,sK1,sK2,X0_58) ),
% 6.34/1.50      inference(instantiation,[status(thm)],[c_817]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_2063,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK1) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK1) != iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK1) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_2062]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3833,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
% 6.34/1.50      | u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_3513,c_38,c_39,c_40,c_1669,c_2063]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3834,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | k2_partfun1(u1_struct_0(X0_58),u1_struct_0(sK1),sK2,u1_struct_0(X1_58)) = k2_tmap_1(X0_58,sK1,sK2,X1_58)
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_3833]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3846,plain,
% 6.34/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_58)) = k2_tmap_1(sK0,sK1,sK2,X0_58)
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK0) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_3834]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_26,negated_conjecture,
% 6.34/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 6.34/1.50      inference(cnf_transformation,[],[f66]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_825,negated_conjecture,
% 6.34/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_26]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1354,plain,
% 6.34/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_5,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | ~ v1_funct_1(X0)
% 6.34/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.34/1.50      inference(cnf_transformation,[],[f50]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_622,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 6.34/1.50      | sK2 != X0 ),
% 6.34/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_28]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_623,plain,
% 6.34/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.34/1.50      | k2_partfun1(X0,X1,sK2,X2) = k7_relat_1(sK2,X2) ),
% 6.34/1.50      inference(unflattening,[status(thm)],[c_622]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_813,plain,
% 6.34/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 6.34/1.50      | k2_partfun1(X0_56,X1_56,sK2,X2_56) = k7_relat_1(sK2,X2_56) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_623]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1366,plain,
% 6.34/1.50      ( k2_partfun1(X0_56,X1_56,sK2,X2_56) = k7_relat_1(sK2,X2_56)
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3129,plain,
% 6.34/1.50      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k7_relat_1(sK2,X0_56) ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_1354,c_1366]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3847,plain,
% 6.34/1.50      ( k2_tmap_1(sK0,sK1,sK2,X0_58) = k7_relat_1(sK2,u1_struct_0(X0_58))
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK0) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top ),
% 6.34/1.50      inference(demodulation,[status(thm)],[c_3846,c_3129]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_34,negated_conjecture,
% 6.34/1.50      ( ~ v2_struct_0(sK0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f58]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_35,plain,
% 6.34/1.50      ( v2_struct_0(sK0) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_33,negated_conjecture,
% 6.34/1.50      ( v2_pre_topc(sK0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f59]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_36,plain,
% 6.34/1.50      ( v2_pre_topc(sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_32,negated_conjecture,
% 6.34/1.50      ( l1_pre_topc(sK0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f60]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_37,plain,
% 6.34/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_43,plain,
% 6.34/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3852,plain,
% 6.34/1.50      ( k2_tmap_1(sK0,sK1,sK2,X0_58) = k7_relat_1(sK2,u1_struct_0(X0_58))
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_3847,c_35,c_36,c_37,c_43]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3861,plain,
% 6.34/1.50      ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_1352,c_3852]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_15,negated_conjecture,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 6.34/1.50      inference(cnf_transformation,[],[f77]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_836,negated_conjecture,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1346,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_16,negated_conjecture,
% 6.34/1.50      ( sK5 = sK7 ),
% 6.34/1.50      inference(cnf_transformation,[],[f76]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_835,negated_conjecture,
% 6.34/1.50      ( sK5 = sK7 ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_17,negated_conjecture,
% 6.34/1.50      ( sK5 = sK6 ),
% 6.34/1.50      inference(cnf_transformation,[],[f75]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_834,negated_conjecture,
% 6.34/1.50      ( sK5 = sK6 ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1369,plain,
% 6.34/1.50      ( sK6 = sK7 ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_834,c_835]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1413,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_1346,c_835,c_1369]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3904,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 6.34/1.50      inference(demodulation,[status(thm)],[c_3861,c_1413]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_21,negated_conjecture,
% 6.34/1.50      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 6.34/1.50      inference(cnf_transformation,[],[f71]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_830,negated_conjecture,
% 6.34/1.50      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_10,plain,
% 6.34/1.50      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 6.34/1.50      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 6.34/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 6.34/1.50      | ~ m1_pre_topc(X5,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 6.34/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X5)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | ~ v1_funct_1(X3) ),
% 6.34/1.50      inference(cnf_transformation,[],[f81]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_549,plain,
% 6.34/1.50      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 6.34/1.50      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 6.34/1.50      | ~ m1_pre_topc(X5,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 6.34/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X5)
% 6.34/1.50      | ~ v1_funct_1(X3)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 6.34/1.50      | sK2 != X3 ),
% 6.34/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_550,plain,
% 6.34/1.50      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | ~ v1_funct_1(sK2)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(unflattening,[status(thm)],[c_549]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_554,plain,
% 6.34/1.50      ( v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 6.34/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 6.34/1.50      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_550,c_28]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_555,plain,
% 6.34/1.50      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_554]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_814,plain,
% 6.34/1.50      ( ~ r1_tmap_1(X0_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X0_58),X0_55)
% 6.34/1.50      | ~ r1_tmap_1(X3_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X3_58),X0_55)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X2_58,X0_58,X3_58),X1_58,k2_tmap_1(X2_58,X1_58,sK2,k1_tsep_1(X2_58,X0_58,X3_58)),X0_55)
% 6.34/1.50      | ~ m1_pre_topc(X0_58,X2_58)
% 6.34/1.50      | ~ m1_pre_topc(X3_58,X2_58)
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X3_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X2_58,X0_58,X3_58)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 6.34/1.50      | ~ v2_pre_topc(X1_58)
% 6.34/1.50      | ~ v2_pre_topc(X2_58)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | ~ l1_pre_topc(X2_58)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X0_58)
% 6.34/1.50      | v2_struct_0(X2_58)
% 6.34/1.50      | v2_struct_0(X3_58)
% 6.34/1.50      | u1_struct_0(X2_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_555]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1365,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1)
% 6.34/1.50      | r1_tmap_1(X2_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X2_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X3_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X3_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X3_58),X1_58,k2_tmap_1(X0_58,X1_58,sK2,k1_tsep_1(X0_58,X2_58,X3_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X3_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X3_58) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3581,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK1) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK1) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK1) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_1365]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1670,plain,
% 6.34/1.50      ( ~ r1_tmap_1(X0_58,sK1,k2_tmap_1(X1_58,sK1,sK2,X0_58),X0_55)
% 6.34/1.50      | ~ r1_tmap_1(X2_58,sK1,k2_tmap_1(X1_58,sK1,sK2,X2_58),X0_55)
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X1_58,X0_58,X2_58),sK1,k2_tmap_1(X1_58,sK1,sK2,k1_tsep_1(X1_58,X0_58,X2_58)),X0_55)
% 6.34/1.50      | ~ m1_pre_topc(X0_58,X1_58)
% 6.34/1.50      | ~ m1_pre_topc(X2_58,X1_58)
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X2_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X1_58,X0_58,X2_58)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(sK1))))
% 6.34/1.50      | ~ v2_pre_topc(X1_58)
% 6.34/1.50      | ~ v2_pre_topc(sK1)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | ~ l1_pre_topc(sK1)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X0_58)
% 6.34/1.50      | v2_struct_0(X2_58)
% 6.34/1.50      | v2_struct_0(sK1)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(instantiation,[status(thm)],[c_814]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1679,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK1) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK1) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK1) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_5317,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_3581,c_38,c_39,c_40]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_5318,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X2_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X2_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_5317]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_5338,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(sK0,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK0) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_5318]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_14445,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(sK0,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_5338,c_35,c_36,c_37,c_43]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_14446,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(sK0,sK1,sK2,X1_58),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_14445]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_14521,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_830,c_14446]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_22,negated_conjecture,
% 6.34/1.50      ( m1_pre_topc(sK4,sK0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f70]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_829,negated_conjecture,
% 6.34/1.50      ( m1_pre_topc(sK4,sK0) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1350,plain,
% 6.34/1.50      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3860,plain,
% 6.34/1.50      ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_1350,c_3852]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_8,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0,X1)
% 6.34/1.50      | ~ m1_pre_topc(X2,X1)
% 6.34/1.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2) ),
% 6.34/1.50      inference(cnf_transformation,[],[f54]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_840,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0_58,X1_58)
% 6.34/1.50      | ~ m1_pre_topc(X2_58,X1_58)
% 6.34/1.50      | m1_pre_topc(k1_tsep_1(X1_58,X0_58,X2_58),X1_58)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X0_58)
% 6.34/1.50      | v2_struct_0(X2_58) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1342,plain,
% 6.34/1.50      ( m1_pre_topc(X0_58,X1_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X1_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(k1_tsep_1(X1_58,X0_58,X2_58),X1_58) = iProver_top
% 6.34/1.50      | l1_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_2340,plain,
% 6.34/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK0,sK0) = iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_830,c_1342]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_25,negated_conjecture,
% 6.34/1.50      ( ~ v2_struct_0(sK3) ),
% 6.34/1.50      inference(cnf_transformation,[],[f67]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_44,plain,
% 6.34/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_45,plain,
% 6.34/1.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_23,negated_conjecture,
% 6.34/1.50      ( ~ v2_struct_0(sK4) ),
% 6.34/1.50      inference(cnf_transformation,[],[f69]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_46,plain,
% 6.34/1.50      ( v2_struct_0(sK4) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_47,plain,
% 6.34/1.50      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_2701,plain,
% 6.34/1.50      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_2340,c_35,c_37,c_44,c_45,c_46,c_47]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3862,plain,
% 6.34/1.50      ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0)) ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_2701,c_3852]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_4,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | v4_relat_1(X0,X1) ),
% 6.34/1.50      inference(cnf_transformation,[],[f49]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1,plain,
% 6.34/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 6.34/1.50      | ~ v4_relat_1(X0,X1)
% 6.34/1.50      | ~ v1_relat_1(X0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f45]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_335,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 6.34/1.50      | ~ v1_relat_1(X0) ),
% 6.34/1.50      inference(resolution,[status(thm)],[c_4,c_1]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | v1_relat_1(X0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f48]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_339,plain,
% 6.34/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 6.34/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_335,c_3]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_340,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | r1_tarski(k1_relat_1(X0),X1) ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_339]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_2,plain,
% 6.34/1.50      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 6.34/1.50      | ~ v1_relat_1(X0)
% 6.34/1.50      | k7_relat_1(X0,X1) = X0 ),
% 6.34/1.50      inference(cnf_transformation,[],[f47]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_356,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | ~ v1_relat_1(X0)
% 6.34/1.50      | k7_relat_1(X0,X1) = X0 ),
% 6.34/1.50      inference(resolution,[status(thm)],[c_340,c_2]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_360,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.50      | k7_relat_1(X0,X1) = X0 ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_356,c_3]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_818,plain,
% 6.34/1.50      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 6.34/1.50      | k7_relat_1(X0_55,X0_56) = X0_55 ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_360]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1361,plain,
% 6.34/1.50      ( k7_relat_1(X0_55,X0_56) = X0_55
% 6.34/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3665,plain,
% 6.34/1.50      ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_1354,c_1361]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3879,plain,
% 6.34/1.50      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_3862,c_3665]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_14534,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK0)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(light_normalisation,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_14521,c_830,c_3860,c_3861,c_3879]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_6,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0,X1)
% 6.34/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 6.34/1.50      | m1_subset_1(X2,u1_struct_0(X1))
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0) ),
% 6.34/1.50      inference(cnf_transformation,[],[f51]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_841,plain,
% 6.34/1.50      ( ~ m1_pre_topc(X0_58,X1_58)
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58))
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X0_58) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1736,plain,
% 6.34/1.50      ( ~ m1_pre_topc(sK3,sK0)
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK0))
% 6.34/1.50      | ~ l1_pre_topc(sK0)
% 6.34/1.50      | v2_struct_0(sK3)
% 6.34/1.50      | v2_struct_0(sK0) ),
% 6.34/1.50      inference(instantiation,[status(thm)],[c_841]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1737,plain,
% 6.34/1.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK0)) = iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_1736]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_16036,plain,
% 6.34/1.50      ( m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_14534,c_35,c_37,c_44,c_45,c_46,c_47,c_1737]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_16037,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_16036]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_16047,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top
% 6.34/1.50      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_3904,c_16037]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_12,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 6.34/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X5,X2)
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 6.34/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X5)
% 6.34/1.50      | ~ v1_funct_1(X3) ),
% 6.34/1.50      inference(cnf_transformation,[],[f85]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_421,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 6.34/1.50      | ~ m1_pre_topc(X5,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 6.34/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X5)
% 6.34/1.50      | ~ v1_funct_1(X3)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 6.34/1.50      | sK2 != X3 ),
% 6.34/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_422,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | ~ v1_funct_1(sK2)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(unflattening,[status(thm)],[c_421]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_426,plain,
% 6.34/1.50      ( v2_struct_0(X4)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 6.34/1.50      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_422,c_28]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_427,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_426]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_816,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X0_58),X0_55)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2_58,X0_58,X3_58),X1_58,k2_tmap_1(X2_58,X1_58,sK2,k1_tsep_1(X2_58,X0_58,X3_58)),X0_55)
% 6.34/1.50      | ~ m1_pre_topc(X0_58,X2_58)
% 6.34/1.50      | ~ m1_pre_topc(X3_58,X2_58)
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X3_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X2_58,X0_58,X3_58)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 6.34/1.50      | ~ v2_pre_topc(X1_58)
% 6.34/1.50      | ~ v2_pre_topc(X2_58)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | ~ l1_pre_topc(X2_58)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X0_58)
% 6.34/1.50      | v2_struct_0(X2_58)
% 6.34/1.50      | v2_struct_0(X3_58)
% 6.34/1.50      | u1_struct_0(X2_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_427]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1363,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1)
% 6.34/1.50      | r1_tmap_1(X2_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X2_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X3_58),X1_58,k2_tmap_1(X0_58,X1_58,sK2,k1_tsep_1(X0_58,X2_58,X3_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X3_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X3_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X3_58) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3536,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK1) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK1) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK1) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_1363]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3948,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
% 6.34/1.50      | u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_3536,c_38,c_39,c_40,c_1669,c_1677]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3949,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X1_58,X2_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X1_58,X2_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X1_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_3948]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3968,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK0) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_3949]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_8404,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_3968,c_35,c_36,c_37,c_43]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_8405,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X0_58,X1_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_58,X1_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X0_58,X1_58))) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_8404]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_8452,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_830,c_8405]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_8462,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK0)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(light_normalisation,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_8452,c_830,c_3861,c_3879]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_9162,plain,
% 6.34/1.50      ( m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) = iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_8462,c_35,c_37,c_44,c_45,c_46,c_47,c_1737]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_9163,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_9162]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_11,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 6.34/1.50      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 6.34/1.50      | ~ m1_pre_topc(X5,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 6.34/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X5)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | ~ v1_funct_1(X3) ),
% 6.34/1.50      inference(cnf_transformation,[],[f83]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_487,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 6.34/1.50      | ~ m1_pre_topc(X5,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 6.34/1.50      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 6.34/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X5)
% 6.34/1.50      | ~ v1_funct_1(X3)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1)
% 6.34/1.50      | sK2 != X3 ),
% 6.34/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_488,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | ~ v1_funct_1(sK2)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(unflattening,[status(thm)],[c_487]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_490,plain,
% 6.34/1.50      ( v2_struct_0(X4)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 6.34/1.50      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_488,c_28]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_491,plain,
% 6.34/1.50      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 6.34/1.50      | ~ m1_pre_topc(X0,X2)
% 6.34/1.50      | ~ m1_pre_topc(X4,X2)
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 6.34/1.50      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 6.34/1.50      | ~ v2_pre_topc(X1)
% 6.34/1.50      | ~ v2_pre_topc(X2)
% 6.34/1.50      | ~ l1_pre_topc(X1)
% 6.34/1.50      | ~ l1_pre_topc(X2)
% 6.34/1.50      | v2_struct_0(X1)
% 6.34/1.50      | v2_struct_0(X0)
% 6.34/1.50      | v2_struct_0(X2)
% 6.34/1.50      | v2_struct_0(X4)
% 6.34/1.50      | u1_struct_0(X2) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_490]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_815,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,X1_58,k2_tmap_1(X2_58,X1_58,sK2,X0_58),X0_55)
% 6.34/1.50      | ~ r1_tmap_1(k1_tsep_1(X2_58,X3_58,X0_58),X1_58,k2_tmap_1(X2_58,X1_58,sK2,k1_tsep_1(X2_58,X3_58,X0_58)),X0_55)
% 6.34/1.50      | ~ m1_pre_topc(X0_58,X2_58)
% 6.34/1.50      | ~ m1_pre_topc(X3_58,X2_58)
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X0_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(X3_58))
% 6.34/1.50      | ~ m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X2_58,X3_58,X0_58)))
% 6.34/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_58),u1_struct_0(X1_58))))
% 6.34/1.50      | ~ v2_pre_topc(X1_58)
% 6.34/1.50      | ~ v2_pre_topc(X2_58)
% 6.34/1.50      | ~ l1_pre_topc(X1_58)
% 6.34/1.50      | ~ l1_pre_topc(X2_58)
% 6.34/1.50      | v2_struct_0(X1_58)
% 6.34/1.50      | v2_struct_0(X0_58)
% 6.34/1.50      | v2_struct_0(X2_58)
% 6.34/1.50      | v2_struct_0(X3_58)
% 6.34/1.50      | u1_struct_0(X2_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_491]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1364,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | u1_struct_0(X1_58) != u1_struct_0(sK1)
% 6.34/1.50      | r1_tmap_1(X2_58,X1_58,k2_tmap_1(X0_58,X1_58,sK2,X2_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X3_58,X2_58),X1_58,k2_tmap_1(X0_58,X1_58,sK2,k1_tsep_1(X0_58,X3_58,X2_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X3_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X3_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X3_58,X2_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X1_58)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X1_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X3_58) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3559,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X1_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X2_58,X1_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X1_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK1) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK1) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK1) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_1364]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_4615,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X1_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X1_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X2_58,X1_58)),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
% 6.34/1.50      | u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_3559,c_38,c_39,c_40]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_4616,plain,
% 6.34/1.50      ( u1_struct_0(X0_58) != u1_struct_0(sK0)
% 6.34/1.50      | r1_tmap_1(X1_58,sK1,k2_tmap_1(X0_58,sK1,sK2,X1_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(X0_58,X2_58,X1_58),sK1,k2_tmap_1(X0_58,sK1,sK2,k1_tsep_1(X0_58,X2_58,X1_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X2_58,X0_58) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X2_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(X0_58,X2_58,X1_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | l1_pre_topc(X0_58) != iProver_top
% 6.34/1.50      | v2_struct_0(X2_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_4615]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_4633,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X1_58,X0_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_58,X0_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X1_58,X0_58))) != iProver_top
% 6.34/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 6.34/1.50      | v2_pre_topc(sK0) != iProver_top
% 6.34/1.50      | l1_pre_topc(sK0) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(sK0) = iProver_top ),
% 6.34/1.50      inference(equality_resolution,[status(thm)],[c_4616]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_10368,plain,
% 6.34/1.50      ( v2_struct_0(X0_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X1_58,X0_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_58,X0_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X1_58,X0_58))) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_4633,c_35,c_36,c_37,c_43]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_10369,plain,
% 6.34/1.50      ( r1_tmap_1(X0_58,sK1,k2_tmap_1(sK0,sK1,sK2,X0_58),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(k1_tsep_1(sK0,X1_58,X0_58),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_58,X0_58)),X0_55) != iProver_top
% 6.34/1.50      | m1_pre_topc(X0_58,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(X1_58,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X0_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(X1_58)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,X1_58,X0_58))) != iProver_top
% 6.34/1.50      | v2_struct_0(X1_58) = iProver_top
% 6.34/1.50      | v2_struct_0(X0_58) = iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_10368]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_10428,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_830,c_10369]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_10438,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) = iProver_top
% 6.34/1.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 6.34/1.50      | m1_pre_topc(sK4,sK0) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK0)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top
% 6.34/1.50      | v2_struct_0(sK3) = iProver_top
% 6.34/1.50      | v2_struct_0(sK4) = iProver_top ),
% 6.34/1.50      inference(light_normalisation,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_10428,c_830,c_3860,c_3879]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_11398,plain,
% 6.34/1.50      ( m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_10438,c_35,c_37,c_44,c_45,c_46,c_47,c_1737]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_11399,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,X0_55) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_55) = iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(X0_55,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(renaming,[status(thm)],[c_11398]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_13,negated_conjecture,
% 6.34/1.50      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 6.34/1.50      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 6.34/1.50      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 6.34/1.50      inference(cnf_transformation,[],[f79]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_838,negated_conjecture,
% 6.34/1.50      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 6.34/1.50      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 6.34/1.50      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1344,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1422,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_1344,c_835,c_1369]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3890,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
% 6.34/1.50      inference(demodulation,[status(thm)],[c_3860,c_1422]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3915,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_3890,c_3861]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_11408,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 6.34/1.50      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_11399,c_3915]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_18,negated_conjecture,
% 6.34/1.50      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 6.34/1.50      inference(cnf_transformation,[],[f74]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_50,plain,
% 6.34/1.50      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_19,negated_conjecture,
% 6.34/1.50      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 6.34/1.50      inference(cnf_transformation,[],[f73]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_832,negated_conjecture,
% 6.34/1.50      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_19]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1348,plain,
% 6.34/1.50      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1394,plain,
% 6.34/1.50      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_1348,c_1369]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_11612,plain,
% 6.34/1.50      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 6.34/1.50      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
% 6.34/1.50      inference(global_propositional_subsumption,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_11408,c_50,c_1394]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_11619,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 6.34/1.50      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 6.34/1.50      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 6.34/1.50      inference(superposition,[status(thm)],[c_9163,c_11612]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_14,negated_conjecture,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 6.34/1.50      inference(cnf_transformation,[],[f78]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_837,negated_conjecture,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 6.34/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1345,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 6.34/1.50      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_1408,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 6.34/1.50      inference(light_normalisation,[status(thm)],[c_1345,c_835]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(c_3889,plain,
% 6.34/1.50      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 6.34/1.50      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) = iProver_top ),
% 6.34/1.50      inference(demodulation,[status(thm)],[c_3860,c_1408]) ).
% 6.34/1.50  
% 6.34/1.50  cnf(contradiction,plain,
% 6.34/1.50      ( $false ),
% 6.34/1.50      inference(minisat,
% 6.34/1.50                [status(thm)],
% 6.34/1.50                [c_16047,c_11619,c_3889,c_1394,c_50]) ).
% 6.34/1.50  
% 6.34/1.50  
% 6.34/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.34/1.50  
% 6.34/1.50  ------                               Statistics
% 6.34/1.50  
% 6.34/1.50  ------ General
% 6.34/1.50  
% 6.34/1.50  abstr_ref_over_cycles:                  0
% 6.34/1.50  abstr_ref_under_cycles:                 0
% 6.34/1.50  gc_basic_clause_elim:                   0
% 6.34/1.50  forced_gc_time:                         0
% 6.34/1.50  parsing_time:                           0.012
% 6.34/1.50  unif_index_cands_time:                  0.
% 6.34/1.50  unif_index_add_time:                    0.
% 6.34/1.50  orderings_time:                         0.
% 6.34/1.50  out_proof_time:                         0.021
% 6.34/1.50  total_time:                             0.68
% 6.34/1.50  num_of_symbols:                         59
% 6.34/1.50  num_of_terms:                           10324
% 6.34/1.50  
% 6.34/1.50  ------ Preprocessing
% 6.34/1.50  
% 6.34/1.50  num_of_splits:                          0
% 6.34/1.50  num_of_split_atoms:                     0
% 6.34/1.50  num_of_reused_defs:                     0
% 6.34/1.50  num_eq_ax_congr_red:                    10
% 6.34/1.50  num_of_sem_filtered_clauses:            1
% 6.34/1.50  num_of_subtypes:                        4
% 6.34/1.50  monotx_restored_types:                  1
% 6.34/1.50  sat_num_of_epr_types:                   0
% 6.34/1.50  sat_num_of_non_cyclic_types:            0
% 6.34/1.50  sat_guarded_non_collapsed_types:        0
% 6.34/1.50  num_pure_diseq_elim:                    0
% 6.34/1.50  simp_replaced_by:                       0
% 6.34/1.50  res_preprocessed:                       163
% 6.34/1.50  prep_upred:                             0
% 6.34/1.50  prep_unflattend:                        5
% 6.34/1.50  smt_new_axioms:                         0
% 6.34/1.50  pred_elim_cands:                        6
% 6.34/1.50  pred_elim:                              5
% 6.34/1.50  pred_elim_cl:                           6
% 6.34/1.50  pred_elim_cycles:                       7
% 6.34/1.50  merged_defs:                            0
% 6.34/1.50  merged_defs_ncl:                        0
% 6.34/1.50  bin_hyper_res:                          0
% 6.34/1.50  prep_cycles:                            4
% 6.34/1.50  pred_elim_time:                         0.025
% 6.34/1.50  splitting_time:                         0.
% 6.34/1.50  sem_filter_time:                        0.
% 6.34/1.50  monotx_time:                            0.001
% 6.34/1.50  subtype_inf_time:                       0.003
% 6.34/1.50  
% 6.34/1.50  ------ Problem properties
% 6.34/1.50  
% 6.34/1.50  clauses:                                29
% 6.34/1.50  conjectures:                            20
% 6.34/1.50  epr:                                    12
% 6.34/1.50  horn:                                   20
% 6.34/1.50  ground:                                 20
% 6.34/1.50  unary:                                  17
% 6.34/1.50  binary:                                 4
% 6.34/1.50  lits:                                   114
% 6.34/1.50  lits_eq:                                14
% 6.34/1.50  fd_pure:                                0
% 6.34/1.50  fd_pseudo:                              0
% 6.34/1.50  fd_cond:                                0
% 6.34/1.50  fd_pseudo_cond:                         0
% 6.34/1.50  ac_symbols:                             0
% 6.34/1.50  
% 6.34/1.50  ------ Propositional Solver
% 6.34/1.50  
% 6.34/1.50  prop_solver_calls:                      28
% 6.34/1.50  prop_fast_solver_calls:                 2443
% 6.34/1.50  smt_solver_calls:                       0
% 6.34/1.50  smt_fast_solver_calls:                  0
% 6.34/1.50  prop_num_of_clauses:                    4603
% 6.34/1.50  prop_preprocess_simplified:             9088
% 6.34/1.50  prop_fo_subsumed:                       189
% 6.34/1.50  prop_solver_time:                       0.
% 6.34/1.50  smt_solver_time:                        0.
% 6.34/1.50  smt_fast_solver_time:                   0.
% 6.34/1.50  prop_fast_solver_time:                  0.
% 6.34/1.50  prop_unsat_core_time:                   0.001
% 6.34/1.50  
% 6.34/1.50  ------ QBF
% 6.34/1.50  
% 6.34/1.50  qbf_q_res:                              0
% 6.34/1.50  qbf_num_tautologies:                    0
% 6.34/1.50  qbf_prep_cycles:                        0
% 6.34/1.50  
% 6.34/1.50  ------ BMC1
% 6.34/1.50  
% 6.34/1.50  bmc1_current_bound:                     -1
% 6.34/1.50  bmc1_last_solved_bound:                 -1
% 6.34/1.50  bmc1_unsat_core_size:                   -1
% 6.34/1.50  bmc1_unsat_core_parents_size:           -1
% 6.34/1.50  bmc1_merge_next_fun:                    0
% 6.34/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.34/1.50  
% 6.34/1.50  ------ Instantiation
% 6.34/1.50  
% 6.34/1.50  inst_num_of_clauses:                    1179
% 6.34/1.50  inst_num_in_passive:                    101
% 6.34/1.50  inst_num_in_active:                     796
% 6.34/1.50  inst_num_in_unprocessed:                282
% 6.34/1.50  inst_num_of_loops:                      820
% 6.34/1.50  inst_num_of_learning_restarts:          0
% 6.34/1.50  inst_num_moves_active_passive:          21
% 6.34/1.50  inst_lit_activity:                      0
% 6.34/1.50  inst_lit_activity_moves:                0
% 6.34/1.50  inst_num_tautologies:                   0
% 6.34/1.50  inst_num_prop_implied:                  0
% 6.34/1.50  inst_num_existing_simplified:           0
% 6.34/1.50  inst_num_eq_res_simplified:             0
% 6.34/1.50  inst_num_child_elim:                    0
% 6.34/1.50  inst_num_of_dismatching_blockings:      174
% 6.34/1.50  inst_num_of_non_proper_insts:           1071
% 6.34/1.50  inst_num_of_duplicates:                 0
% 6.34/1.50  inst_inst_num_from_inst_to_res:         0
% 6.34/1.50  inst_dismatching_checking_time:         0.
% 6.34/1.50  
% 6.34/1.50  ------ Resolution
% 6.34/1.50  
% 6.34/1.50  res_num_of_clauses:                     0
% 6.34/1.50  res_num_in_passive:                     0
% 6.34/1.50  res_num_in_active:                      0
% 6.34/1.50  res_num_of_loops:                       167
% 6.34/1.50  res_forward_subset_subsumed:            172
% 6.34/1.50  res_backward_subset_subsumed:           0
% 6.34/1.50  res_forward_subsumed:                   0
% 6.34/1.50  res_backward_subsumed:                  0
% 6.34/1.50  res_forward_subsumption_resolution:     0
% 6.34/1.50  res_backward_subsumption_resolution:    0
% 6.34/1.50  res_clause_to_clause_subsumption:       2434
% 6.34/1.50  res_orphan_elimination:                 0
% 6.34/1.50  res_tautology_del:                      56
% 6.34/1.50  res_num_eq_res_simplified:              0
% 6.34/1.50  res_num_sel_changes:                    0
% 6.34/1.50  res_moves_from_active_to_pass:          0
% 6.34/1.50  
% 6.34/1.50  ------ Superposition
% 6.34/1.51  
% 6.34/1.51  sup_time_total:                         0.
% 6.34/1.51  sup_time_generating:                    0.
% 6.34/1.51  sup_time_sim_full:                      0.
% 6.34/1.51  sup_time_sim_immed:                     0.
% 6.34/1.51  
% 6.34/1.51  sup_num_of_clauses:                     362
% 6.34/1.51  sup_num_in_active:                      153
% 6.34/1.51  sup_num_in_passive:                     209
% 6.34/1.51  sup_num_of_loops:                       163
% 6.34/1.51  sup_fw_superposition:                   314
% 6.34/1.51  sup_bw_superposition:                   63
% 6.34/1.51  sup_immediate_simplified:               216
% 6.34/1.51  sup_given_eliminated:                   0
% 6.34/1.51  comparisons_done:                       0
% 6.34/1.51  comparisons_avoided:                    0
% 6.34/1.51  
% 6.34/1.51  ------ Simplifications
% 6.34/1.51  
% 6.34/1.51  
% 6.34/1.51  sim_fw_subset_subsumed:                 12
% 6.34/1.51  sim_bw_subset_subsumed:                 9
% 6.34/1.51  sim_fw_subsumed:                        0
% 6.34/1.51  sim_bw_subsumed:                        0
% 6.34/1.51  sim_fw_subsumption_res:                 0
% 6.34/1.51  sim_bw_subsumption_res:                 5
% 6.34/1.51  sim_tautology_del:                      6
% 6.34/1.51  sim_eq_tautology_del:                   20
% 6.34/1.51  sim_eq_res_simp:                        0
% 6.34/1.51  sim_fw_demodulated:                     1
% 6.34/1.51  sim_bw_demodulated:                     3
% 6.34/1.51  sim_light_normalised:                   205
% 6.34/1.51  sim_joinable_taut:                      0
% 6.34/1.51  sim_joinable_simp:                      0
% 6.34/1.51  sim_ac_normalised:                      0
% 6.34/1.51  sim_smt_subsumption:                    0
% 6.34/1.51  
%------------------------------------------------------------------------------
