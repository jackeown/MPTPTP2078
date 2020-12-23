%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:16 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1578)

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
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f30,f38,f37,f36,f35,f34,f33,f32,f31])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

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
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f39])).

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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
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
    inference(equality_resolution,[],[f48])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f62,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f46])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
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
    inference(equality_resolution,[],[f47])).

fof(f75,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f71,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_768,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1279,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f45])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_322,plain,
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
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_323,plain,
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
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_327,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_25])).

cnf(c_328,plain,
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
    inference(renaming,[status(thm)],[c_327])).

cnf(c_758,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X2_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | u1_struct_0(X1_56) != u1_struct_0(sK0)
    | u1_struct_0(X2_56) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X2_56),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,X2_56,sK2,X0_56) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_1289,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK2,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,sK2,X2_56)
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_2310,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1289])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_784,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1570,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1727,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK1)
    | u1_struct_0(X1_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,sK1,sK2,X0_56) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1728,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1727])).

cnf(c_2817,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2310,c_35,c_36,c_37,c_1570,c_1728])).

cnf(c_2818,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_2817])).

cnf(c_2830,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(sK0,sK1,sK2,X0_56)
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2818])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_766,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1281,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_569,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK2,X2) = k7_relat_1(sK2,X2) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_754,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_1293,plain,
    ( k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2238,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) = k7_relat_1(sK2,X0_54) ),
    inference(superposition,[status(thm)],[c_1281,c_1293])).

cnf(c_2831,plain,
    ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2830,c_2238])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2836,plain,
    ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
    | m1_pre_topc(X0_56,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2831,c_32,c_33,c_34,c_40])).

cnf(c_2845,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1279,c_2836])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_777,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1273,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_13,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_776,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_14,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_775,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1296,plain,
    ( sK6 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_775,c_776])).

cnf(c_1344,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1273,c_776,c_1296])).

cnf(c_2916,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2845,c_1344])).

cnf(c_18,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_771,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_495,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_496,plain,
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
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_500,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_25])).

cnf(c_501,plain,
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
    inference(renaming,[status(thm)],[c_500])).

cnf(c_755,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(X3_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X3_56),X0_53)
    | r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | u1_struct_0(X2_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_1292,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(X3_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X3_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X3_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X2_56,X3_56)),X0_53) = iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X3_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X3_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_2571,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1292])).

cnf(c_1571,plain,
    ( ~ r1_tmap_1(X0_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(X2_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X2_56),X0_53)
    | r1_tmap_1(k1_tsep_1(X1_56,X0_56,X2_56),sK1,k2_tmap_1(X1_56,sK1,sK2,k1_tsep_1(X1_56,X0_56,X2_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X2_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X1_56,X0_56,X2_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(sK1)
    | u1_struct_0(X1_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1580,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_3203,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2571,c_35,c_36,c_37])).

cnf(c_3204,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3203])).

cnf(c_3224,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3204])).

cnf(c_3542,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3224,c_32,c_33,c_34,c_40])).

cnf(c_3543,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3542])).

cnf(c_3558,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) != iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_3543])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_770,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1277,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_2844,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_1277,c_2836])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_780,plain,
    ( m1_pre_topc(X0_56,X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1270,plain,
    ( m1_pre_topc(X0_56,X0_56) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_2846,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1270,c_2836])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_2,c_1,c_0])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k7_relat_1(X0_53,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_306])).

cnf(c_1288,plain,
    ( k7_relat_1(X0_53,X0_54) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_2654,plain,
    ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_1281,c_1288])).

cnf(c_2849,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2846,c_2654])).

cnf(c_3047,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2849,c_34])).

cnf(c_3572,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3558,c_771,c_2844,c_2845,c_3047])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_44,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3699,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3572,c_41,c_42,c_43,c_44])).

cnf(c_3711,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_3699])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_367,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_368,plain,
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
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_372,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_25])).

cnf(c_373,plain,
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
    inference(renaming,[status(thm)],[c_372])).

cnf(c_757,plain,
    ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | u1_struct_0(X2_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_1290,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X3_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X2_56,X3_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X3_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X3_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_2451,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1290])).

cnf(c_3089,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_35,c_36,c_37,c_1570,c_1578])).

cnf(c_3090,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3089])).

cnf(c_3109,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3090])).

cnf(c_3229,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3109,c_32,c_33,c_34,c_40])).

cnf(c_3230,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3229])).

cnf(c_3244,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) = iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_3230])).

cnf(c_3246,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3244,c_771,c_2845,c_3047])).

cnf(c_3341,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3246,c_41,c_42,c_43,c_44])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_433,plain,
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
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_434,plain,
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
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_436,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_25])).

cnf(c_437,plain,
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
    inference(renaming,[status(thm)],[c_436])).

cnf(c_756,plain,
    ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(k1_tsep_1(X2_56,X3_56,X0_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X3_56,X0_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X3_56,X0_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | u1_struct_0(X2_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_437])).

cnf(c_1291,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X3_56,X2_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X3_56,X2_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X3_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X3_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_2474,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1291])).

cnf(c_3114,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_35,c_36,c_37])).

cnf(c_3115,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3114])).

cnf(c_3132,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3115])).

cnf(c_3353,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3132,c_32,c_33,c_34,c_40])).

cnf(c_3354,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3353])).

cnf(c_3366,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_3354])).

cnf(c_3368,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3366,c_771,c_2844,c_3047])).

cnf(c_3433,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3368,c_41,c_42,c_43,c_44])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_779,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1271,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_1353,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1271,c_776,c_1296])).

cnf(c_2902,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2844,c_1353])).

cnf(c_2990,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2902,c_2845])).

cnf(c_3444,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3433,c_2990])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_47,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_773,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1275,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_1321,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1275,c_1296])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_772,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1276,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_1324,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1276,c_776])).

cnf(c_3447,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_47,c_1321,c_1324])).

cnf(c_3448,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_3447])).

cnf(c_3454,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_3448])).

cnf(c_11,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_778,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1272,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_1339,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1272,c_776])).

cnf(c_2901,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2844,c_1339])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3711,c_3454,c_2901,c_1324,c_1321,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:19:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.34/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.99  
% 2.34/0.99  ------  iProver source info
% 2.34/0.99  
% 2.34/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.99  git: non_committed_changes: false
% 2.34/0.99  git: last_make_outside_of_git: false
% 2.34/0.99  
% 2.34/0.99  ------ 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options
% 2.34/0.99  
% 2.34/0.99  --out_options                           all
% 2.34/0.99  --tptp_safe_out                         true
% 2.34/0.99  --problem_path                          ""
% 2.34/0.99  --include_path                          ""
% 2.34/0.99  --clausifier                            res/vclausify_rel
% 2.34/0.99  --clausifier_options                    --mode clausify
% 2.34/0.99  --stdin                                 false
% 2.34/0.99  --stats_out                             all
% 2.34/0.99  
% 2.34/0.99  ------ General Options
% 2.34/0.99  
% 2.34/0.99  --fof                                   false
% 2.34/0.99  --time_out_real                         305.
% 2.34/0.99  --time_out_virtual                      -1.
% 2.34/0.99  --symbol_type_check                     false
% 2.34/0.99  --clausify_out                          false
% 2.34/0.99  --sig_cnt_out                           false
% 2.34/0.99  --trig_cnt_out                          false
% 2.34/0.99  --trig_cnt_out_tolerance                1.
% 2.34/0.99  --trig_cnt_out_sk_spl                   false
% 2.34/0.99  --abstr_cl_out                          false
% 2.34/0.99  
% 2.34/0.99  ------ Global Options
% 2.34/0.99  
% 2.34/0.99  --schedule                              default
% 2.34/0.99  --add_important_lit                     false
% 2.34/0.99  --prop_solver_per_cl                    1000
% 2.34/0.99  --min_unsat_core                        false
% 2.34/0.99  --soft_assumptions                      false
% 2.34/0.99  --soft_lemma_size                       3
% 2.34/0.99  --prop_impl_unit_size                   0
% 2.34/0.99  --prop_impl_unit                        []
% 2.34/0.99  --share_sel_clauses                     true
% 2.34/0.99  --reset_solvers                         false
% 2.34/0.99  --bc_imp_inh                            [conj_cone]
% 2.34/0.99  --conj_cone_tolerance                   3.
% 2.34/0.99  --extra_neg_conj                        none
% 2.34/0.99  --large_theory_mode                     true
% 2.34/0.99  --prolific_symb_bound                   200
% 2.34/0.99  --lt_threshold                          2000
% 2.34/0.99  --clause_weak_htbl                      true
% 2.34/0.99  --gc_record_bc_elim                     false
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing Options
% 2.34/0.99  
% 2.34/0.99  --preprocessing_flag                    true
% 2.34/0.99  --time_out_prep_mult                    0.1
% 2.34/0.99  --splitting_mode                        input
% 2.34/0.99  --splitting_grd                         true
% 2.34/0.99  --splitting_cvd                         false
% 2.34/0.99  --splitting_cvd_svl                     false
% 2.34/0.99  --splitting_nvd                         32
% 2.34/0.99  --sub_typing                            true
% 2.34/0.99  --prep_gs_sim                           true
% 2.34/0.99  --prep_unflatten                        true
% 2.34/0.99  --prep_res_sim                          true
% 2.34/0.99  --prep_upred                            true
% 2.34/0.99  --prep_sem_filter                       exhaustive
% 2.34/0.99  --prep_sem_filter_out                   false
% 2.34/0.99  --pred_elim                             true
% 2.34/0.99  --res_sim_input                         true
% 2.34/0.99  --eq_ax_congr_red                       true
% 2.34/0.99  --pure_diseq_elim                       true
% 2.34/0.99  --brand_transform                       false
% 2.34/0.99  --non_eq_to_eq                          false
% 2.34/0.99  --prep_def_merge                        true
% 2.34/0.99  --prep_def_merge_prop_impl              false
% 2.34/0.99  --prep_def_merge_mbd                    true
% 2.34/0.99  --prep_def_merge_tr_red                 false
% 2.34/0.99  --prep_def_merge_tr_cl                  false
% 2.34/0.99  --smt_preprocessing                     true
% 2.34/0.99  --smt_ac_axioms                         fast
% 2.34/0.99  --preprocessed_out                      false
% 2.34/0.99  --preprocessed_stats                    false
% 2.34/0.99  
% 2.34/0.99  ------ Abstraction refinement Options
% 2.34/0.99  
% 2.34/0.99  --abstr_ref                             []
% 2.34/0.99  --abstr_ref_prep                        false
% 2.34/0.99  --abstr_ref_until_sat                   false
% 2.34/0.99  --abstr_ref_sig_restrict                funpre
% 2.34/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.99  --abstr_ref_under                       []
% 2.34/0.99  
% 2.34/0.99  ------ SAT Options
% 2.34/0.99  
% 2.34/0.99  --sat_mode                              false
% 2.34/0.99  --sat_fm_restart_options                ""
% 2.34/0.99  --sat_gr_def                            false
% 2.34/0.99  --sat_epr_types                         true
% 2.34/0.99  --sat_non_cyclic_types                  false
% 2.34/0.99  --sat_finite_models                     false
% 2.34/0.99  --sat_fm_lemmas                         false
% 2.34/0.99  --sat_fm_prep                           false
% 2.34/0.99  --sat_fm_uc_incr                        true
% 2.34/0.99  --sat_out_model                         small
% 2.34/0.99  --sat_out_clauses                       false
% 2.34/0.99  
% 2.34/0.99  ------ QBF Options
% 2.34/0.99  
% 2.34/0.99  --qbf_mode                              false
% 2.34/0.99  --qbf_elim_univ                         false
% 2.34/0.99  --qbf_dom_inst                          none
% 2.34/0.99  --qbf_dom_pre_inst                      false
% 2.34/0.99  --qbf_sk_in                             false
% 2.34/0.99  --qbf_pred_elim                         true
% 2.34/0.99  --qbf_split                             512
% 2.34/0.99  
% 2.34/0.99  ------ BMC1 Options
% 2.34/0.99  
% 2.34/0.99  --bmc1_incremental                      false
% 2.34/0.99  --bmc1_axioms                           reachable_all
% 2.34/0.99  --bmc1_min_bound                        0
% 2.34/0.99  --bmc1_max_bound                        -1
% 2.34/0.99  --bmc1_max_bound_default                -1
% 2.34/0.99  --bmc1_symbol_reachability              true
% 2.34/0.99  --bmc1_property_lemmas                  false
% 2.34/0.99  --bmc1_k_induction                      false
% 2.34/0.99  --bmc1_non_equiv_states                 false
% 2.34/0.99  --bmc1_deadlock                         false
% 2.34/0.99  --bmc1_ucm                              false
% 2.34/0.99  --bmc1_add_unsat_core                   none
% 2.34/0.99  --bmc1_unsat_core_children              false
% 2.34/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.99  --bmc1_out_stat                         full
% 2.34/0.99  --bmc1_ground_init                      false
% 2.34/0.99  --bmc1_pre_inst_next_state              false
% 2.34/0.99  --bmc1_pre_inst_state                   false
% 2.34/0.99  --bmc1_pre_inst_reach_state             false
% 2.34/0.99  --bmc1_out_unsat_core                   false
% 2.34/0.99  --bmc1_aig_witness_out                  false
% 2.34/0.99  --bmc1_verbose                          false
% 2.34/0.99  --bmc1_dump_clauses_tptp                false
% 2.34/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.99  --bmc1_dump_file                        -
% 2.34/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.99  --bmc1_ucm_extend_mode                  1
% 2.34/0.99  --bmc1_ucm_init_mode                    2
% 2.34/0.99  --bmc1_ucm_cone_mode                    none
% 2.34/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.99  --bmc1_ucm_relax_model                  4
% 2.34/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.99  --bmc1_ucm_layered_model                none
% 2.34/0.99  --bmc1_ucm_max_lemma_size               10
% 2.34/0.99  
% 2.34/0.99  ------ AIG Options
% 2.34/0.99  
% 2.34/0.99  --aig_mode                              false
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation Options
% 2.34/0.99  
% 2.34/0.99  --instantiation_flag                    true
% 2.34/0.99  --inst_sos_flag                         false
% 2.34/0.99  --inst_sos_phase                        true
% 2.34/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel_side                     num_symb
% 2.34/0.99  --inst_solver_per_active                1400
% 2.34/0.99  --inst_solver_calls_frac                1.
% 2.34/0.99  --inst_passive_queue_type               priority_queues
% 2.34/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.99  --inst_passive_queues_freq              [25;2]
% 2.34/0.99  --inst_dismatching                      true
% 2.34/0.99  --inst_eager_unprocessed_to_passive     true
% 2.34/0.99  --inst_prop_sim_given                   true
% 2.34/0.99  --inst_prop_sim_new                     false
% 2.34/0.99  --inst_subs_new                         false
% 2.34/0.99  --inst_eq_res_simp                      false
% 2.34/0.99  --inst_subs_given                       false
% 2.34/0.99  --inst_orphan_elimination               true
% 2.34/0.99  --inst_learning_loop_flag               true
% 2.34/0.99  --inst_learning_start                   3000
% 2.34/0.99  --inst_learning_factor                  2
% 2.34/0.99  --inst_start_prop_sim_after_learn       3
% 2.34/0.99  --inst_sel_renew                        solver
% 2.34/0.99  --inst_lit_activity_flag                true
% 2.34/0.99  --inst_restr_to_given                   false
% 2.34/0.99  --inst_activity_threshold               500
% 2.34/0.99  --inst_out_proof                        true
% 2.34/0.99  
% 2.34/0.99  ------ Resolution Options
% 2.34/0.99  
% 2.34/0.99  --resolution_flag                       true
% 2.34/0.99  --res_lit_sel                           adaptive
% 2.34/0.99  --res_lit_sel_side                      none
% 2.34/0.99  --res_ordering                          kbo
% 2.34/0.99  --res_to_prop_solver                    active
% 2.34/0.99  --res_prop_simpl_new                    false
% 2.34/0.99  --res_prop_simpl_given                  true
% 2.34/0.99  --res_passive_queue_type                priority_queues
% 2.34/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.99  --res_passive_queues_freq               [15;5]
% 2.34/0.99  --res_forward_subs                      full
% 2.34/0.99  --res_backward_subs                     full
% 2.34/0.99  --res_forward_subs_resolution           true
% 2.34/0.99  --res_backward_subs_resolution          true
% 2.34/0.99  --res_orphan_elimination                true
% 2.34/0.99  --res_time_limit                        2.
% 2.34/0.99  --res_out_proof                         true
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Options
% 2.34/0.99  
% 2.34/0.99  --superposition_flag                    true
% 2.34/0.99  --sup_passive_queue_type                priority_queues
% 2.34/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.99  --demod_completeness_check              fast
% 2.34/0.99  --demod_use_ground                      true
% 2.34/0.99  --sup_to_prop_solver                    passive
% 2.34/0.99  --sup_prop_simpl_new                    true
% 2.34/0.99  --sup_prop_simpl_given                  true
% 2.34/0.99  --sup_fun_splitting                     false
% 2.34/0.99  --sup_smt_interval                      50000
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Simplification Setup
% 2.34/0.99  
% 2.34/0.99  --sup_indices_passive                   []
% 2.34/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_full_bw                           [BwDemod]
% 2.34/0.99  --sup_immed_triv                        [TrivRules]
% 2.34/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_immed_bw_main                     []
% 2.34/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  
% 2.34/0.99  ------ Combination Options
% 2.34/0.99  
% 2.34/0.99  --comb_res_mult                         3
% 2.34/0.99  --comb_sup_mult                         2
% 2.34/0.99  --comb_inst_mult                        10
% 2.34/0.99  
% 2.34/0.99  ------ Debug Options
% 2.34/0.99  
% 2.34/0.99  --dbg_backtrace                         false
% 2.34/0.99  --dbg_dump_prop_clauses                 false
% 2.34/0.99  --dbg_dump_prop_clauses_file            -
% 2.34/0.99  --dbg_out_stat                          false
% 2.34/0.99  ------ Parsing...
% 2.34/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/0.99  ------ Proving...
% 2.34/0.99  ------ Problem Properties 
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  clauses                                 28
% 2.34/0.99  conjectures                             20
% 2.34/0.99  EPR                                     13
% 2.34/0.99  Horn                                    21
% 2.34/0.99  unary                                   17
% 2.34/0.99  binary                                  5
% 2.34/0.99  lits                                    102
% 2.34/0.99  lits eq                                 14
% 2.34/0.99  fd_pure                                 0
% 2.34/0.99  fd_pseudo                               0
% 2.34/0.99  fd_cond                                 0
% 2.34/0.99  fd_pseudo_cond                          0
% 2.34/0.99  AC symbols                              0
% 2.34/0.99  
% 2.34/0.99  ------ Schedule dynamic 5 is on 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  ------ 
% 2.34/0.99  Current options:
% 2.34/0.99  ------ 
% 2.34/0.99  
% 2.34/0.99  ------ Input Options
% 2.34/0.99  
% 2.34/0.99  --out_options                           all
% 2.34/0.99  --tptp_safe_out                         true
% 2.34/0.99  --problem_path                          ""
% 2.34/0.99  --include_path                          ""
% 2.34/0.99  --clausifier                            res/vclausify_rel
% 2.34/0.99  --clausifier_options                    --mode clausify
% 2.34/0.99  --stdin                                 false
% 2.34/0.99  --stats_out                             all
% 2.34/0.99  
% 2.34/0.99  ------ General Options
% 2.34/0.99  
% 2.34/0.99  --fof                                   false
% 2.34/0.99  --time_out_real                         305.
% 2.34/0.99  --time_out_virtual                      -1.
% 2.34/0.99  --symbol_type_check                     false
% 2.34/0.99  --clausify_out                          false
% 2.34/0.99  --sig_cnt_out                           false
% 2.34/0.99  --trig_cnt_out                          false
% 2.34/0.99  --trig_cnt_out_tolerance                1.
% 2.34/0.99  --trig_cnt_out_sk_spl                   false
% 2.34/0.99  --abstr_cl_out                          false
% 2.34/0.99  
% 2.34/0.99  ------ Global Options
% 2.34/0.99  
% 2.34/0.99  --schedule                              default
% 2.34/0.99  --add_important_lit                     false
% 2.34/0.99  --prop_solver_per_cl                    1000
% 2.34/0.99  --min_unsat_core                        false
% 2.34/0.99  --soft_assumptions                      false
% 2.34/0.99  --soft_lemma_size                       3
% 2.34/0.99  --prop_impl_unit_size                   0
% 2.34/0.99  --prop_impl_unit                        []
% 2.34/0.99  --share_sel_clauses                     true
% 2.34/0.99  --reset_solvers                         false
% 2.34/0.99  --bc_imp_inh                            [conj_cone]
% 2.34/0.99  --conj_cone_tolerance                   3.
% 2.34/0.99  --extra_neg_conj                        none
% 2.34/0.99  --large_theory_mode                     true
% 2.34/0.99  --prolific_symb_bound                   200
% 2.34/0.99  --lt_threshold                          2000
% 2.34/0.99  --clause_weak_htbl                      true
% 2.34/0.99  --gc_record_bc_elim                     false
% 2.34/0.99  
% 2.34/0.99  ------ Preprocessing Options
% 2.34/0.99  
% 2.34/0.99  --preprocessing_flag                    true
% 2.34/0.99  --time_out_prep_mult                    0.1
% 2.34/0.99  --splitting_mode                        input
% 2.34/0.99  --splitting_grd                         true
% 2.34/0.99  --splitting_cvd                         false
% 2.34/0.99  --splitting_cvd_svl                     false
% 2.34/0.99  --splitting_nvd                         32
% 2.34/0.99  --sub_typing                            true
% 2.34/0.99  --prep_gs_sim                           true
% 2.34/0.99  --prep_unflatten                        true
% 2.34/0.99  --prep_res_sim                          true
% 2.34/0.99  --prep_upred                            true
% 2.34/0.99  --prep_sem_filter                       exhaustive
% 2.34/0.99  --prep_sem_filter_out                   false
% 2.34/0.99  --pred_elim                             true
% 2.34/0.99  --res_sim_input                         true
% 2.34/0.99  --eq_ax_congr_red                       true
% 2.34/0.99  --pure_diseq_elim                       true
% 2.34/0.99  --brand_transform                       false
% 2.34/0.99  --non_eq_to_eq                          false
% 2.34/0.99  --prep_def_merge                        true
% 2.34/0.99  --prep_def_merge_prop_impl              false
% 2.34/0.99  --prep_def_merge_mbd                    true
% 2.34/0.99  --prep_def_merge_tr_red                 false
% 2.34/0.99  --prep_def_merge_tr_cl                  false
% 2.34/0.99  --smt_preprocessing                     true
% 2.34/0.99  --smt_ac_axioms                         fast
% 2.34/0.99  --preprocessed_out                      false
% 2.34/0.99  --preprocessed_stats                    false
% 2.34/0.99  
% 2.34/0.99  ------ Abstraction refinement Options
% 2.34/0.99  
% 2.34/0.99  --abstr_ref                             []
% 2.34/0.99  --abstr_ref_prep                        false
% 2.34/0.99  --abstr_ref_until_sat                   false
% 2.34/0.99  --abstr_ref_sig_restrict                funpre
% 2.34/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.99  --abstr_ref_under                       []
% 2.34/0.99  
% 2.34/0.99  ------ SAT Options
% 2.34/0.99  
% 2.34/0.99  --sat_mode                              false
% 2.34/0.99  --sat_fm_restart_options                ""
% 2.34/0.99  --sat_gr_def                            false
% 2.34/0.99  --sat_epr_types                         true
% 2.34/0.99  --sat_non_cyclic_types                  false
% 2.34/0.99  --sat_finite_models                     false
% 2.34/0.99  --sat_fm_lemmas                         false
% 2.34/0.99  --sat_fm_prep                           false
% 2.34/0.99  --sat_fm_uc_incr                        true
% 2.34/0.99  --sat_out_model                         small
% 2.34/0.99  --sat_out_clauses                       false
% 2.34/0.99  
% 2.34/0.99  ------ QBF Options
% 2.34/0.99  
% 2.34/0.99  --qbf_mode                              false
% 2.34/0.99  --qbf_elim_univ                         false
% 2.34/0.99  --qbf_dom_inst                          none
% 2.34/0.99  --qbf_dom_pre_inst                      false
% 2.34/0.99  --qbf_sk_in                             false
% 2.34/0.99  --qbf_pred_elim                         true
% 2.34/0.99  --qbf_split                             512
% 2.34/0.99  
% 2.34/0.99  ------ BMC1 Options
% 2.34/0.99  
% 2.34/0.99  --bmc1_incremental                      false
% 2.34/0.99  --bmc1_axioms                           reachable_all
% 2.34/0.99  --bmc1_min_bound                        0
% 2.34/0.99  --bmc1_max_bound                        -1
% 2.34/0.99  --bmc1_max_bound_default                -1
% 2.34/0.99  --bmc1_symbol_reachability              true
% 2.34/0.99  --bmc1_property_lemmas                  false
% 2.34/0.99  --bmc1_k_induction                      false
% 2.34/0.99  --bmc1_non_equiv_states                 false
% 2.34/0.99  --bmc1_deadlock                         false
% 2.34/0.99  --bmc1_ucm                              false
% 2.34/0.99  --bmc1_add_unsat_core                   none
% 2.34/0.99  --bmc1_unsat_core_children              false
% 2.34/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.99  --bmc1_out_stat                         full
% 2.34/0.99  --bmc1_ground_init                      false
% 2.34/0.99  --bmc1_pre_inst_next_state              false
% 2.34/0.99  --bmc1_pre_inst_state                   false
% 2.34/0.99  --bmc1_pre_inst_reach_state             false
% 2.34/0.99  --bmc1_out_unsat_core                   false
% 2.34/0.99  --bmc1_aig_witness_out                  false
% 2.34/0.99  --bmc1_verbose                          false
% 2.34/0.99  --bmc1_dump_clauses_tptp                false
% 2.34/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.99  --bmc1_dump_file                        -
% 2.34/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.99  --bmc1_ucm_extend_mode                  1
% 2.34/0.99  --bmc1_ucm_init_mode                    2
% 2.34/0.99  --bmc1_ucm_cone_mode                    none
% 2.34/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.99  --bmc1_ucm_relax_model                  4
% 2.34/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.99  --bmc1_ucm_layered_model                none
% 2.34/0.99  --bmc1_ucm_max_lemma_size               10
% 2.34/0.99  
% 2.34/0.99  ------ AIG Options
% 2.34/0.99  
% 2.34/0.99  --aig_mode                              false
% 2.34/0.99  
% 2.34/0.99  ------ Instantiation Options
% 2.34/0.99  
% 2.34/0.99  --instantiation_flag                    true
% 2.34/0.99  --inst_sos_flag                         false
% 2.34/0.99  --inst_sos_phase                        true
% 2.34/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.99  --inst_lit_sel_side                     none
% 2.34/0.99  --inst_solver_per_active                1400
% 2.34/0.99  --inst_solver_calls_frac                1.
% 2.34/0.99  --inst_passive_queue_type               priority_queues
% 2.34/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.99  --inst_passive_queues_freq              [25;2]
% 2.34/0.99  --inst_dismatching                      true
% 2.34/0.99  --inst_eager_unprocessed_to_passive     true
% 2.34/0.99  --inst_prop_sim_given                   true
% 2.34/0.99  --inst_prop_sim_new                     false
% 2.34/0.99  --inst_subs_new                         false
% 2.34/0.99  --inst_eq_res_simp                      false
% 2.34/0.99  --inst_subs_given                       false
% 2.34/0.99  --inst_orphan_elimination               true
% 2.34/0.99  --inst_learning_loop_flag               true
% 2.34/0.99  --inst_learning_start                   3000
% 2.34/0.99  --inst_learning_factor                  2
% 2.34/0.99  --inst_start_prop_sim_after_learn       3
% 2.34/0.99  --inst_sel_renew                        solver
% 2.34/0.99  --inst_lit_activity_flag                true
% 2.34/0.99  --inst_restr_to_given                   false
% 2.34/0.99  --inst_activity_threshold               500
% 2.34/0.99  --inst_out_proof                        true
% 2.34/0.99  
% 2.34/0.99  ------ Resolution Options
% 2.34/0.99  
% 2.34/0.99  --resolution_flag                       false
% 2.34/0.99  --res_lit_sel                           adaptive
% 2.34/0.99  --res_lit_sel_side                      none
% 2.34/0.99  --res_ordering                          kbo
% 2.34/0.99  --res_to_prop_solver                    active
% 2.34/0.99  --res_prop_simpl_new                    false
% 2.34/0.99  --res_prop_simpl_given                  true
% 2.34/0.99  --res_passive_queue_type                priority_queues
% 2.34/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.99  --res_passive_queues_freq               [15;5]
% 2.34/0.99  --res_forward_subs                      full
% 2.34/0.99  --res_backward_subs                     full
% 2.34/0.99  --res_forward_subs_resolution           true
% 2.34/0.99  --res_backward_subs_resolution          true
% 2.34/0.99  --res_orphan_elimination                true
% 2.34/0.99  --res_time_limit                        2.
% 2.34/0.99  --res_out_proof                         true
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Options
% 2.34/0.99  
% 2.34/0.99  --superposition_flag                    true
% 2.34/0.99  --sup_passive_queue_type                priority_queues
% 2.34/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.99  --demod_completeness_check              fast
% 2.34/0.99  --demod_use_ground                      true
% 2.34/0.99  --sup_to_prop_solver                    passive
% 2.34/0.99  --sup_prop_simpl_new                    true
% 2.34/0.99  --sup_prop_simpl_given                  true
% 2.34/0.99  --sup_fun_splitting                     false
% 2.34/0.99  --sup_smt_interval                      50000
% 2.34/0.99  
% 2.34/0.99  ------ Superposition Simplification Setup
% 2.34/0.99  
% 2.34/0.99  --sup_indices_passive                   []
% 2.34/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_full_bw                           [BwDemod]
% 2.34/0.99  --sup_immed_triv                        [TrivRules]
% 2.34/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_immed_bw_main                     []
% 2.34/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.99  
% 2.34/0.99  ------ Combination Options
% 2.34/0.99  
% 2.34/0.99  --comb_res_mult                         3
% 2.34/0.99  --comb_sup_mult                         2
% 2.34/0.99  --comb_inst_mult                        10
% 2.34/0.99  
% 2.34/0.99  ------ Debug Options
% 2.34/0.99  
% 2.34/0.99  --dbg_backtrace                         false
% 2.34/0.99  --dbg_dump_prop_clauses                 false
% 2.34/0.99  --dbg_dump_prop_clauses_file            -
% 2.34/0.99  --dbg_out_stat                          false
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  ------ Proving...
% 2.34/0.99  
% 2.34/0.99  
% 2.34/0.99  % SZS status Theorem for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.99  
% 2.34/0.99  fof(f9,conjecture,(
% 2.34/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f10,negated_conjecture,(
% 2.34/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.34/0.99    inference(negated_conjecture,[],[f9])).
% 2.34/0.99  
% 2.34/0.99  fof(f25,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f10])).
% 2.34/0.99  
% 2.34/0.99  fof(f26,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f25])).
% 2.34/0.99  
% 2.34/0.99  fof(f29,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.99    inference(nnf_transformation,[],[f26])).
% 2.34/0.99  
% 2.34/0.99  fof(f30,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f29])).
% 2.34/0.99  
% 2.34/0.99  fof(f38,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK7 = X5 & X5 = X6 & m1_subset_1(sK7,u1_struct_0(X4)))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f37,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK6 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f36,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f35,plain,(
% 2.34/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK4) = X0 & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f34,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f33,plain,(
% 2.34/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) | ~r1_tmap_1(X0,X1,sK2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)) | r1_tmap_1(X0,X1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f32,plain,(
% 2.34/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) | ~r1_tmap_1(X0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)) | r1_tmap_1(X0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f31,plain,(
% 2.34/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & k1_tsep_1(sK0,X3,X4) = sK0 & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.34/0.99    introduced(choice_axiom,[])).
% 2.34/0.99  
% 2.34/0.99  fof(f39,plain,(
% 2.34/0.99    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & k1_tsep_1(sK0,sK3,sK4) = sK0 & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.34/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f30,f38,f37,f36,f35,f34,f33,f32,f31])).
% 2.34/0.99  
% 2.34/0.99  fof(f60,plain,(
% 2.34/0.99    m1_pre_topc(sK3,sK0)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f6,axiom,(
% 2.34/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f20,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f6])).
% 2.34/0.99  
% 2.34/0.99  fof(f21,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f20])).
% 2.34/0.99  
% 2.34/0.99  fof(f45,plain,(
% 2.34/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f21])).
% 2.34/0.99  
% 2.34/0.99  fof(f57,plain,(
% 2.34/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f56,plain,(
% 2.34/0.99    v1_funct_1(sK2)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f53,plain,(
% 2.34/0.99    ~v2_struct_0(sK1)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f54,plain,(
% 2.34/0.99    v2_pre_topc(sK1)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f55,plain,(
% 2.34/0.99    l1_pre_topc(sK1)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f58,plain,(
% 2.34/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f4,axiom,(
% 2.34/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f16,plain,(
% 2.34/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.34/0.99    inference(ennf_transformation,[],[f4])).
% 2.34/0.99  
% 2.34/0.99  fof(f17,plain,(
% 2.34/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.34/0.99    inference(flattening,[],[f16])).
% 2.34/0.99  
% 2.34/0.99  fof(f43,plain,(
% 2.34/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f17])).
% 2.34/0.99  
% 2.34/0.99  fof(f50,plain,(
% 2.34/0.99    ~v2_struct_0(sK0)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f51,plain,(
% 2.34/0.99    v2_pre_topc(sK0)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f52,plain,(
% 2.34/0.99    l1_pre_topc(sK0)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f69,plain,(
% 2.34/0.99    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f68,plain,(
% 2.34/0.99    sK5 = sK7),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f67,plain,(
% 2.34/0.99    sK5 = sK6),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f63,plain,(
% 2.34/0.99    k1_tsep_1(sK0,sK3,sK4) = sK0),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f7,axiom,(
% 2.34/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f22,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.34/0.99    inference(ennf_transformation,[],[f7])).
% 2.34/0.99  
% 2.34/0.99  fof(f23,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f22])).
% 2.34/0.99  
% 2.34/0.99  fof(f27,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(nnf_transformation,[],[f23])).
% 2.34/0.99  
% 2.34/0.99  fof(f28,plain,(
% 2.34/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.34/0.99    inference(flattening,[],[f27])).
% 2.34/0.99  
% 2.34/0.99  fof(f48,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f28])).
% 2.34/0.99  
% 2.34/0.99  fof(f72,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f48])).
% 2.34/0.99  
% 2.34/0.99  fof(f73,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f72])).
% 2.34/0.99  
% 2.34/0.99  fof(f62,plain,(
% 2.34/0.99    m1_pre_topc(sK4,sK0)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f8,axiom,(
% 2.34/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f24,plain,(
% 2.34/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.34/0.99    inference(ennf_transformation,[],[f8])).
% 2.34/0.99  
% 2.34/0.99  fof(f49,plain,(
% 2.34/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f24])).
% 2.34/0.99  
% 2.34/0.99  fof(f3,axiom,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f11,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.34/0.99    inference(pure_predicate_removal,[],[f3])).
% 2.34/0.99  
% 2.34/0.99  fof(f15,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f11])).
% 2.34/0.99  
% 2.34/0.99  fof(f42,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f15])).
% 2.34/0.99  
% 2.34/0.99  fof(f1,axiom,(
% 2.34/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f12,plain,(
% 2.34/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.34/0.99    inference(ennf_transformation,[],[f1])).
% 2.34/0.99  
% 2.34/0.99  fof(f13,plain,(
% 2.34/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.34/0.99    inference(flattening,[],[f12])).
% 2.34/0.99  
% 2.34/0.99  fof(f40,plain,(
% 2.34/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f13])).
% 2.34/0.99  
% 2.34/0.99  fof(f2,axiom,(
% 2.34/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.34/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.99  
% 2.34/0.99  fof(f14,plain,(
% 2.34/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.34/0.99    inference(ennf_transformation,[],[f2])).
% 2.34/0.99  
% 2.34/0.99  fof(f41,plain,(
% 2.34/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.34/0.99    inference(cnf_transformation,[],[f14])).
% 2.34/0.99  
% 2.34/0.99  fof(f59,plain,(
% 2.34/0.99    ~v2_struct_0(sK3)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f61,plain,(
% 2.34/0.99    ~v2_struct_0(sK4)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f46,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f28])).
% 2.34/0.99  
% 2.34/0.99  fof(f76,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f46])).
% 2.34/0.99  
% 2.34/0.99  fof(f77,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f76])).
% 2.34/0.99  
% 2.34/0.99  fof(f47,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(cnf_transformation,[],[f28])).
% 2.34/0.99  
% 2.34/0.99  fof(f74,plain,(
% 2.34/0.99    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f47])).
% 2.34/0.99  
% 2.34/0.99  fof(f75,plain,(
% 2.34/0.99    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.34/0.99    inference(equality_resolution,[],[f74])).
% 2.34/0.99  
% 2.34/0.99  fof(f71,plain,(
% 2.34/0.99    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f66,plain,(
% 2.34/0.99    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f65,plain,(
% 2.34/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f64,plain,(
% 2.34/0.99    m1_subset_1(sK5,u1_struct_0(sK0))),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  fof(f70,plain,(
% 2.34/0.99    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 2.34/0.99    inference(cnf_transformation,[],[f39])).
% 2.34/0.99  
% 2.34/0.99  cnf(c_21,negated_conjecture,
% 2.34/0.99      ( m1_pre_topc(sK3,sK0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_768,negated_conjecture,
% 2.34/0.99      ( m1_pre_topc(sK3,sK0) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1279,plain,
% 2.34/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_5,plain,
% 2.34/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.34/0.99      | ~ m1_pre_topc(X3,X1)
% 2.34/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | ~ v1_funct_1(X0)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_24,negated_conjecture,
% 2.34/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.34/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_322,plain,
% 2.34/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.34/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X3)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X3)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X3)
% 2.34/0.99      | ~ v1_funct_1(X2)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.34/0.99      | sK2 != X2 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_323,plain,
% 2.34/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | ~ v1_funct_1(sK2)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_322]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_25,negated_conjecture,
% 2.34/0.99      ( v1_funct_1(sK2) ),
% 2.34/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_327,plain,
% 2.34/0.99      ( v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.34/0.99      | ~ m1_pre_topc(X0,X1)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_323,c_25]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_328,plain,
% 2.34/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_327]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_758,plain,
% 2.34/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X2_56))))
% 2.34/0.99      | ~ v2_pre_topc(X1_56)
% 2.34/0.99      | ~ v2_pre_topc(X2_56)
% 2.34/0.99      | ~ l1_pre_topc(X1_56)
% 2.34/0.99      | ~ l1_pre_topc(X2_56)
% 2.34/0.99      | v2_struct_0(X1_56)
% 2.34/0.99      | v2_struct_0(X2_56)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK1)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X2_56),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,X2_56,sK2,X0_56) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_328]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1289,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK2,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,sK2,X2_56)
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2310,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.34/0.99      inference(equality_resolution,[status(thm)],[c_1289]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_28,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_35,plain,
% 2.34/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_27,negated_conjecture,
% 2.34/0.99      ( v2_pre_topc(sK1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_36,plain,
% 2.34/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_26,negated_conjecture,
% 2.34/0.99      ( l1_pre_topc(sK1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_37,plain,
% 2.34/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_784,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1570,plain,
% 2.34/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_784]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1727,plain,
% 2.34/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
% 2.34/0.99      | ~ v2_pre_topc(X1_56)
% 2.34/0.99      | ~ v2_pre_topc(sK1)
% 2.34/0.99      | ~ l1_pre_topc(X1_56)
% 2.34/0.99      | ~ l1_pre_topc(sK1)
% 2.34/0.99      | v2_struct_0(X1_56)
% 2.34/0.99      | v2_struct_0(sK1)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,sK1,sK2,X0_56) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_758]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1728,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_1727]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2817,plain,
% 2.34/0.99      ( v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 2.34/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_2310,c_35,c_36,c_37,c_1570,c_1728]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2818,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_2817]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2830,plain,
% 2.34/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(sK0,sK1,sK2,X0_56)
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.34/0.99      | v2_struct_0(sK0) = iProver_top ),
% 2.34/0.99      inference(equality_resolution,[status(thm)],[c_2818]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_23,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.34/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_766,negated_conjecture,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1281,plain,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | ~ v1_funct_1(X0)
% 2.34/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_568,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.34/0.99      | sK2 != X0 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_569,plain,
% 2.34/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.34/0.99      | k2_partfun1(X0,X1,sK2,X2) = k7_relat_1(sK2,X2) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_568]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_754,plain,
% 2.34/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.34/0.99      | k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_569]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1293,plain,
% 2.34/0.99      ( k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54)
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2238,plain,
% 2.34/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) = k7_relat_1(sK2,X0_54) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1281,c_1293]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2831,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.34/0.99      | v2_struct_0(sK0) = iProver_top ),
% 2.34/0.99      inference(demodulation,[status(thm)],[c_2830,c_2238]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_31,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_32,plain,
% 2.34/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_30,negated_conjecture,
% 2.34/0.99      ( v2_pre_topc(sK0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_33,plain,
% 2.34/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_29,negated_conjecture,
% 2.34/0.99      ( l1_pre_topc(sK0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_34,plain,
% 2.34/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_40,plain,
% 2.34/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2836,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_2831,c_32,c_33,c_34,c_40]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2845,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1279,c_2836]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_12,negated_conjecture,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 2.34/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_777,negated_conjecture,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1273,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_13,negated_conjecture,
% 2.34/0.99      ( sK5 = sK7 ),
% 2.34/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_776,negated_conjecture,
% 2.34/0.99      ( sK5 = sK7 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_14,negated_conjecture,
% 2.34/0.99      ( sK5 = sK6 ),
% 2.34/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_775,negated_conjecture,
% 2.34/0.99      ( sK5 = sK6 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1296,plain,
% 2.34/0.99      ( sK6 = sK7 ),
% 2.34/0.99      inference(light_normalisation,[status(thm)],[c_775,c_776]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1344,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 2.34/0.99      inference(light_normalisation,[status(thm)],[c_1273,c_776,c_1296]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2916,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 2.34/0.99      inference(demodulation,[status(thm)],[c_2845,c_1344]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_18,negated_conjecture,
% 2.34/0.99      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 2.34/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_771,negated_conjecture,
% 2.34/0.99      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_6,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.34/0.99      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.34/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_pre_topc(X5,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X5)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v1_funct_1(X3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_495,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.34/0.99      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.34/0.99      | ~ m1_pre_topc(X5,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X5)
% 2.34/0.99      | ~ v1_funct_1(X3)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.34/0.99      | sK2 != X3 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_496,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v1_funct_1(sK2)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_495]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_500,plain,
% 2.34/0.99      ( v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 2.34/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 2.34/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_496,c_25]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_501,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_500]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_755,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
% 2.34/0.99      | ~ r1_tmap_1(X3_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X3_56),X0_53)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
% 2.34/0.99      | ~ m1_pre_topc(X0_56,X2_56)
% 2.34/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 2.34/0.99      | ~ v2_pre_topc(X1_56)
% 2.34/0.99      | ~ v2_pre_topc(X2_56)
% 2.34/0.99      | ~ l1_pre_topc(X1_56)
% 2.34/0.99      | ~ l1_pre_topc(X2_56)
% 2.34/0.99      | v2_struct_0(X1_56)
% 2.34/0.99      | v2_struct_0(X0_56)
% 2.34/0.99      | v2_struct_0(X2_56)
% 2.34/0.99      | v2_struct_0(X3_56)
% 2.34/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_501]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1292,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 2.34/0.99      | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X3_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X3_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X3_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X2_56,X3_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X3_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X3_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X3_56) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2571,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.34/0.99      inference(equality_resolution,[status(thm)],[c_1292]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1571,plain,
% 2.34/0.99      ( ~ r1_tmap_1(X0_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X0_56),X0_53)
% 2.34/0.99      | ~ r1_tmap_1(X2_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X2_56),X0_53)
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X1_56,X0_56,X2_56),sK1,k2_tmap_1(X1_56,sK1,sK2,k1_tsep_1(X1_56,X0_56,X2_56)),X0_53)
% 2.34/0.99      | ~ m1_pre_topc(X0_56,X1_56)
% 2.34/0.99      | ~ m1_pre_topc(X2_56,X1_56)
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X2_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X1_56,X0_56,X2_56)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
% 2.34/0.99      | ~ v2_pre_topc(X1_56)
% 2.34/0.99      | ~ v2_pre_topc(sK1)
% 2.34/0.99      | ~ l1_pre_topc(X1_56)
% 2.34/0.99      | ~ l1_pre_topc(sK1)
% 2.34/0.99      | v2_struct_0(X1_56)
% 2.34/0.99      | v2_struct_0(X0_56)
% 2.34/0.99      | v2_struct_0(X2_56)
% 2.34/0.99      | v2_struct_0(sK1)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(instantiation,[status(thm)],[c_755]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1580,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3203,plain,
% 2.34/0.99      ( v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_2571,c_35,c_36,c_37]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3204,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_3203]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3224,plain,
% 2.34/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK0) = iProver_top ),
% 2.34/0.99      inference(equality_resolution,[status(thm)],[c_3204]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3542,plain,
% 2.34/0.99      ( v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_3224,c_32,c_33,c_34,c_40]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3543,plain,
% 2.34/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_3542]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3558,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.34/0.99      | v2_struct_0(sK3) = iProver_top
% 2.34/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_771,c_3543]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_19,negated_conjecture,
% 2.34/0.99      ( m1_pre_topc(sK4,sK0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_770,negated_conjecture,
% 2.34/0.99      ( m1_pre_topc(sK4,sK0) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1277,plain,
% 2.34/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2844,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1277,c_2836]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_9,plain,
% 2.34/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_780,plain,
% 2.34/0.99      ( m1_pre_topc(X0_56,X0_56) | ~ l1_pre_topc(X0_56) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1270,plain,
% 2.34/0.99      ( m1_pre_topc(X0_56,X0_56) = iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2846,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0))
% 2.34/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1270,c_2836]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | v4_relat_1(X0,X1) ),
% 2.34/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_0,plain,
% 2.34/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.34/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_302,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | ~ v1_relat_1(X0)
% 2.34/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.34/0.99      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | v1_relat_1(X0) ),
% 2.34/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_306,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.34/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_302,c_2,c_1,c_0]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_759,plain,
% 2.34/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.34/0.99      | k7_relat_1(X0_53,X0_54) = X0_53 ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_306]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1288,plain,
% 2.34/0.99      ( k7_relat_1(X0_53,X0_54) = X0_53
% 2.34/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2654,plain,
% 2.34/0.99      ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_1281,c_1288]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2849,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2
% 2.34/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.34/0.99      inference(light_normalisation,[status(thm)],[c_2846,c_2654]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3047,plain,
% 2.34/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_2849,c_34]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3572,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.34/0.99      | v2_struct_0(sK3) = iProver_top
% 2.34/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.34/0.99      inference(light_normalisation,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_3558,c_771,c_2844,c_2845,c_3047]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_22,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_41,plain,
% 2.34/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_42,plain,
% 2.34/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_20,negated_conjecture,
% 2.34/0.99      ( ~ v2_struct_0(sK4) ),
% 2.34/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_43,plain,
% 2.34/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_44,plain,
% 2.34/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3699,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_3572,c_41,c_42,c_43,c_44]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3711,plain,
% 2.34/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top
% 2.34/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.34/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_2916,c_3699]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_8,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 2.34/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X5,X2)
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X5)
% 2.34/0.99      | ~ v1_funct_1(X3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_367,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 2.34/0.99      | ~ m1_pre_topc(X5,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X5)
% 2.34/0.99      | ~ v1_funct_1(X3)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.34/0.99      | sK2 != X3 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_368,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | ~ v1_funct_1(sK2)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_372,plain,
% 2.34/0.99      ( v2_struct_0(X4)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 2.34/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_368,c_25]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_373,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_372]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_757,plain,
% 2.34/0.99      ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
% 2.34/0.99      | ~ m1_pre_topc(X0_56,X2_56)
% 2.34/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 2.34/0.99      | ~ v2_pre_topc(X1_56)
% 2.34/0.99      | ~ v2_pre_topc(X2_56)
% 2.34/0.99      | ~ l1_pre_topc(X1_56)
% 2.34/0.99      | ~ l1_pre_topc(X2_56)
% 2.34/0.99      | v2_struct_0(X1_56)
% 2.34/0.99      | v2_struct_0(X0_56)
% 2.34/0.99      | v2_struct_0(X2_56)
% 2.34/0.99      | v2_struct_0(X3_56)
% 2.34/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_373]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1290,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 2.34/0.99      | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X3_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X2_56,X3_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X3_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X3_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X3_56) = iProver_top ),
% 2.34/0.99      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_2451,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.34/0.99      inference(equality_resolution,[status(thm)],[c_1290]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3089,plain,
% 2.34/0.99      ( v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 2.34/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_2451,c_35,c_36,c_37,c_1570,c_1578]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3090,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_3089]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3109,plain,
% 2.34/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(sK0) != iProver_top
% 2.34/0.99      | l1_pre_topc(sK0) != iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(sK0) = iProver_top ),
% 2.34/0.99      inference(equality_resolution,[status(thm)],[c_3090]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3229,plain,
% 2.34/0.99      ( v2_struct_0(X0_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_3109,c_32,c_33,c_34,c_40]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3230,plain,
% 2.34/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 2.34/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.34/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_3229]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3244,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.34/0.99      | v2_struct_0(sK3) = iProver_top
% 2.34/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.34/0.99      inference(superposition,[status(thm)],[c_771,c_3230]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3246,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.34/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.34/0.99      | v2_struct_0(sK3) = iProver_top
% 2.34/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.34/0.99      inference(light_normalisation,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_3244,c_771,c_2845,c_3047]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_3341,plain,
% 2.34/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_3246,c_41,c_42,c_43,c_44]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_7,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.34/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.34/0.99      | ~ m1_pre_topc(X5,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X5)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | ~ v1_funct_1(X3) ),
% 2.34/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_433,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.34/0.99      | ~ m1_pre_topc(X5,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.34/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X5)
% 2.34/0.99      | ~ v1_funct_1(X3)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.34/0.99      | sK2 != X3 ),
% 2.34/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_434,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | ~ v1_funct_1(sK2)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_436,plain,
% 2.34/0.99      ( v2_struct_0(X4)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 2.34/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(global_propositional_subsumption,
% 2.34/0.99                [status(thm)],
% 2.34/0.99                [c_434,c_25]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_437,plain,
% 2.34/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 2.34/0.99      | ~ m1_pre_topc(X0,X2)
% 2.34/0.99      | ~ m1_pre_topc(X4,X2)
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.34/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.34/0.99      | ~ v2_pre_topc(X1)
% 2.34/0.99      | ~ v2_pre_topc(X2)
% 2.34/0.99      | ~ l1_pre_topc(X1)
% 2.34/0.99      | ~ l1_pre_topc(X2)
% 2.34/0.99      | v2_struct_0(X1)
% 2.34/0.99      | v2_struct_0(X0)
% 2.34/0.99      | v2_struct_0(X2)
% 2.34/0.99      | v2_struct_0(X4)
% 2.34/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(renaming,[status(thm)],[c_436]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_756,plain,
% 2.34/0.99      ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
% 2.34/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_56,X3_56,X0_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X3_56,X0_56)),X0_53)
% 2.34/0.99      | ~ m1_pre_topc(X0_56,X2_56)
% 2.34/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
% 2.34/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X3_56,X0_56)))
% 2.34/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 2.34/0.99      | ~ v2_pre_topc(X1_56)
% 2.34/0.99      | ~ v2_pre_topc(X2_56)
% 2.34/0.99      | ~ l1_pre_topc(X1_56)
% 2.34/0.99      | ~ l1_pre_topc(X2_56)
% 2.34/0.99      | v2_struct_0(X1_56)
% 2.34/0.99      | v2_struct_0(X0_56)
% 2.34/0.99      | v2_struct_0(X2_56)
% 2.34/0.99      | v2_struct_0(X3_56)
% 2.34/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
% 2.34/0.99      inference(subtyping,[status(esa)],[c_437]) ).
% 2.34/0.99  
% 2.34/0.99  cnf(c_1291,plain,
% 2.34/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 2.34/0.99      | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) = iProver_top
% 2.34/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X3_56,X2_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X3_56,X2_56)),X0_53) != iProver_top
% 2.34/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/0.99      | m1_pre_topc(X3_56,X0_56) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
% 2.34/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X3_56,X2_56))) != iProver_top
% 2.34/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 2.34/0.99      | v2_pre_topc(X1_56) != iProver_top
% 2.34/0.99      | v2_pre_topc(X0_56) != iProver_top
% 2.34/0.99      | l1_pre_topc(X0_56) != iProver_top
% 2.34/1.00      | l1_pre_topc(X1_56) != iProver_top
% 2.34/1.00      | v2_struct_0(X0_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X2_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X3_56) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2474,plain,
% 2.34/1.00      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/1.00      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 2.34/1.00      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
% 2.34/1.00      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/1.00      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
% 2.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/1.00      | v2_pre_topc(X0_56) != iProver_top
% 2.34/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.34/1.00      | l1_pre_topc(X0_56) != iProver_top
% 2.34/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.34/1.00      | v2_struct_0(X2_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X0_56) = iProver_top
% 2.34/1.00      | v2_struct_0(sK1) = iProver_top ),
% 2.34/1.00      inference(equality_resolution,[status(thm)],[c_1291]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3114,plain,
% 2.34/1.00      ( v2_struct_0(X0_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X2_56) = iProver_top
% 2.34/1.00      | v2_pre_topc(X0_56) != iProver_top
% 2.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/1.00      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/1.00      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/1.00      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
% 2.34/1.00      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 2.34/1.00      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/1.00      | l1_pre_topc(X0_56) != iProver_top ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_2474,c_35,c_36,c_37]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3115,plain,
% 2.34/1.00      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 2.34/1.00      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 2.34/1.00      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
% 2.34/1.00      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.34/1.00      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
% 2.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 2.34/1.00      | v2_pre_topc(X0_56) != iProver_top
% 2.34/1.00      | l1_pre_topc(X0_56) != iProver_top
% 2.34/1.00      | v2_struct_0(X2_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_3114]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3132,plain,
% 2.34/1.00      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 2.34/1.00      | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
% 2.34/1.00      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/1.00      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
% 2.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.34/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.34/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X0_56) = iProver_top
% 2.34/1.00      | v2_struct_0(sK0) = iProver_top ),
% 2.34/1.00      inference(equality_resolution,[status(thm)],[c_3115]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3353,plain,
% 2.34/1.00      ( v2_struct_0(X0_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 2.34/1.00      | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
% 2.34/1.00      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/1.00      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_3132,c_32,c_33,c_34,c_40]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3354,plain,
% 2.34/1.00      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 2.34/1.00      | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
% 2.34/1.00      | m1_pre_topc(X0_56,sK0) != iProver_top
% 2.34/1.00      | m1_pre_topc(X1_56,sK0) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
% 2.34/1.00      | v2_struct_0(X1_56) = iProver_top
% 2.34/1.00      | v2_struct_0(X0_56) = iProver_top ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_3353]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3366,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) = iProver_top
% 2.34/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.34/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.34/1.00      | v2_struct_0(sK3) = iProver_top
% 2.34/1.00      | v2_struct_0(sK4) = iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_771,c_3354]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3368,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
% 2.34/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.34/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.34/1.00      | v2_struct_0(sK3) = iProver_top
% 2.34/1.00      | v2_struct_0(sK4) = iProver_top ),
% 2.34/1.00      inference(light_normalisation,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_3366,c_771,c_2844,c_3047]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3433,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 2.34/1.00      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_3368,c_41,c_42,c_43,c_44]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_10,negated_conjecture,
% 2.34/1.00      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.34/1.00      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.34/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.34/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_779,negated_conjecture,
% 2.34/1.00      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 2.34/1.00      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.34/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1271,plain,
% 2.34/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1353,plain,
% 2.34/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 2.34/1.00      inference(light_normalisation,[status(thm)],[c_1271,c_776,c_1296]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2902,plain,
% 2.34/1.00      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
% 2.34/1.00      inference(demodulation,[status(thm)],[c_2844,c_1353]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2990,plain,
% 2.34/1.00      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
% 2.34/1.00      inference(light_normalisation,[status(thm)],[c_2902,c_2845]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3444,plain,
% 2.34/1.00      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.34/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.34/1.00      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.34/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3433,c_2990]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_15,negated_conjecture,
% 2.34/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_47,plain,
% 2.34/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_16,negated_conjecture,
% 2.34/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_773,negated_conjecture,
% 2.34/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1275,plain,
% 2.34/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1321,plain,
% 2.34/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.34/1.00      inference(light_normalisation,[status(thm)],[c_1275,c_1296]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_17,negated_conjecture,
% 2.34/1.00      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 2.34/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_772,negated_conjecture,
% 2.34/1.00      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1276,plain,
% 2.34/1.00      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1324,plain,
% 2.34/1.00      ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
% 2.34/1.00      inference(light_normalisation,[status(thm)],[c_1276,c_776]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3447,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top ),
% 2.34/1.00      inference(global_propositional_subsumption,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_3444,c_47,c_1321,c_1324]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3448,plain,
% 2.34/1.00      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 2.34/1.00      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
% 2.34/1.00      inference(renaming,[status(thm)],[c_3447]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_3454,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 2.34/1.00      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 2.34/1.00      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 2.34/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 2.34/1.00      inference(superposition,[status(thm)],[c_3341,c_3448]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_11,negated_conjecture,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.34/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_778,negated_conjecture,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 2.34/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1272,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 2.34/1.00      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_1339,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 2.34/1.00      inference(light_normalisation,[status(thm)],[c_1272,c_776]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(c_2901,plain,
% 2.34/1.00      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 2.34/1.00      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) = iProver_top ),
% 2.34/1.00      inference(demodulation,[status(thm)],[c_2844,c_1339]) ).
% 2.34/1.00  
% 2.34/1.00  cnf(contradiction,plain,
% 2.34/1.00      ( $false ),
% 2.34/1.00      inference(minisat,
% 2.34/1.00                [status(thm)],
% 2.34/1.00                [c_3711,c_3454,c_2901,c_1324,c_1321,c_47]) ).
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/1.00  
% 2.34/1.00  ------                               Statistics
% 2.34/1.00  
% 2.34/1.00  ------ General
% 2.34/1.00  
% 2.34/1.00  abstr_ref_over_cycles:                  0
% 2.34/1.00  abstr_ref_under_cycles:                 0
% 2.34/1.00  gc_basic_clause_elim:                   0
% 2.34/1.00  forced_gc_time:                         0
% 2.34/1.00  parsing_time:                           0.01
% 2.34/1.00  unif_index_cands_time:                  0.
% 2.34/1.00  unif_index_add_time:                    0.
% 2.34/1.00  orderings_time:                         0.
% 2.34/1.00  out_proof_time:                         0.018
% 2.34/1.00  total_time:                             0.182
% 2.34/1.00  num_of_symbols:                         57
% 2.34/1.00  num_of_terms:                           3060
% 2.34/1.00  
% 2.34/1.00  ------ Preprocessing
% 2.34/1.00  
% 2.34/1.00  num_of_splits:                          0
% 2.34/1.00  num_of_split_atoms:                     0
% 2.34/1.00  num_of_reused_defs:                     0
% 2.34/1.00  num_eq_ax_congr_red:                    8
% 2.34/1.00  num_of_sem_filtered_clauses:            1
% 2.34/1.00  num_of_subtypes:                        4
% 2.34/1.00  monotx_restored_types:                  1
% 2.34/1.00  sat_num_of_epr_types:                   0
% 2.34/1.00  sat_num_of_non_cyclic_types:            0
% 2.34/1.00  sat_guarded_non_collapsed_types:        0
% 2.34/1.00  num_pure_diseq_elim:                    0
% 2.34/1.00  simp_replaced_by:                       0
% 2.34/1.00  res_preprocessed:                       157
% 2.34/1.00  prep_upred:                             0
% 2.34/1.00  prep_unflattend:                        5
% 2.34/1.00  smt_new_axioms:                         0
% 2.34/1.00  pred_elim_cands:                        6
% 2.34/1.00  pred_elim:                              4
% 2.34/1.00  pred_elim_cl:                           4
% 2.34/1.00  pred_elim_cycles:                       6
% 2.34/1.00  merged_defs:                            0
% 2.34/1.00  merged_defs_ncl:                        0
% 2.34/1.00  bin_hyper_res:                          0
% 2.34/1.00  prep_cycles:                            4
% 2.34/1.00  pred_elim_time:                         0.011
% 2.34/1.00  splitting_time:                         0.
% 2.34/1.00  sem_filter_time:                        0.
% 2.34/1.00  monotx_time:                            0.001
% 2.34/1.00  subtype_inf_time:                       0.002
% 2.34/1.00  
% 2.34/1.00  ------ Problem properties
% 2.34/1.00  
% 2.34/1.00  clauses:                                28
% 2.34/1.00  conjectures:                            20
% 2.34/1.00  epr:                                    13
% 2.34/1.00  horn:                                   21
% 2.34/1.00  ground:                                 20
% 2.34/1.00  unary:                                  17
% 2.34/1.00  binary:                                 5
% 2.34/1.00  lits:                                   102
% 2.34/1.00  lits_eq:                                14
% 2.34/1.00  fd_pure:                                0
% 2.34/1.00  fd_pseudo:                              0
% 2.34/1.00  fd_cond:                                0
% 2.34/1.00  fd_pseudo_cond:                         0
% 2.34/1.00  ac_symbols:                             0
% 2.34/1.00  
% 2.34/1.00  ------ Propositional Solver
% 2.34/1.00  
% 2.34/1.00  prop_solver_calls:                      27
% 2.34/1.00  prop_fast_solver_calls:                 1624
% 2.34/1.00  smt_solver_calls:                       0
% 2.34/1.00  smt_fast_solver_calls:                  0
% 2.34/1.00  prop_num_of_clauses:                    962
% 2.34/1.00  prop_preprocess_simplified:             4423
% 2.34/1.00  prop_fo_subsumed:                       55
% 2.34/1.00  prop_solver_time:                       0.
% 2.34/1.00  smt_solver_time:                        0.
% 2.34/1.00  smt_fast_solver_time:                   0.
% 2.34/1.00  prop_fast_solver_time:                  0.
% 2.34/1.00  prop_unsat_core_time:                   0.
% 2.34/1.00  
% 2.34/1.00  ------ QBF
% 2.34/1.00  
% 2.34/1.00  qbf_q_res:                              0
% 2.34/1.00  qbf_num_tautologies:                    0
% 2.34/1.00  qbf_prep_cycles:                        0
% 2.34/1.00  
% 2.34/1.00  ------ BMC1
% 2.34/1.00  
% 2.34/1.00  bmc1_current_bound:                     -1
% 2.34/1.00  bmc1_last_solved_bound:                 -1
% 2.34/1.00  bmc1_unsat_core_size:                   -1
% 2.34/1.00  bmc1_unsat_core_parents_size:           -1
% 2.34/1.00  bmc1_merge_next_fun:                    0
% 2.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.34/1.00  
% 2.34/1.00  ------ Instantiation
% 2.34/1.00  
% 2.34/1.00  inst_num_of_clauses:                    336
% 2.34/1.00  inst_num_in_passive:                    62
% 2.34/1.00  inst_num_in_active:                     271
% 2.34/1.00  inst_num_in_unprocessed:                3
% 2.34/1.00  inst_num_of_loops:                      280
% 2.34/1.00  inst_num_of_learning_restarts:          0
% 2.34/1.00  inst_num_moves_active_passive:          5
% 2.34/1.00  inst_lit_activity:                      0
% 2.34/1.00  inst_lit_activity_moves:                0
% 2.34/1.00  inst_num_tautologies:                   0
% 2.34/1.00  inst_num_prop_implied:                  0
% 2.34/1.00  inst_num_existing_simplified:           0
% 2.34/1.00  inst_num_eq_res_simplified:             0
% 2.34/1.00  inst_num_child_elim:                    0
% 2.34/1.00  inst_num_of_dismatching_blockings:      172
% 2.34/1.00  inst_num_of_non_proper_insts:           434
% 2.34/1.00  inst_num_of_duplicates:                 0
% 2.34/1.00  inst_inst_num_from_inst_to_res:         0
% 2.34/1.00  inst_dismatching_checking_time:         0.
% 2.34/1.00  
% 2.34/1.00  ------ Resolution
% 2.34/1.00  
% 2.34/1.00  res_num_of_clauses:                     0
% 2.34/1.00  res_num_in_passive:                     0
% 2.34/1.00  res_num_in_active:                      0
% 2.34/1.00  res_num_of_loops:                       161
% 2.34/1.00  res_forward_subset_subsumed:            87
% 2.34/1.00  res_backward_subset_subsumed:           0
% 2.34/1.00  res_forward_subsumed:                   0
% 2.34/1.00  res_backward_subsumed:                  0
% 2.34/1.00  res_forward_subsumption_resolution:     0
% 2.34/1.00  res_backward_subsumption_resolution:    0
% 2.34/1.00  res_clause_to_clause_subsumption:       244
% 2.34/1.00  res_orphan_elimination:                 0
% 2.34/1.00  res_tautology_del:                      73
% 2.34/1.00  res_num_eq_res_simplified:              0
% 2.34/1.00  res_num_sel_changes:                    0
% 2.34/1.00  res_moves_from_active_to_pass:          0
% 2.34/1.00  
% 2.34/1.00  ------ Superposition
% 2.34/1.00  
% 2.34/1.00  sup_time_total:                         0.
% 2.34/1.00  sup_time_generating:                    0.
% 2.34/1.00  sup_time_sim_full:                      0.
% 2.34/1.00  sup_time_sim_immed:                     0.
% 2.34/1.00  
% 2.34/1.00  sup_num_of_clauses:                     53
% 2.34/1.00  sup_num_in_active:                      51
% 2.34/1.00  sup_num_in_passive:                     2
% 2.34/1.00  sup_num_of_loops:                       54
% 2.34/1.00  sup_fw_superposition:                   24
% 2.34/1.00  sup_bw_superposition:                   11
% 2.34/1.00  sup_immediate_simplified:               11
% 2.34/1.00  sup_given_eliminated:                   0
% 2.34/1.00  comparisons_done:                       0
% 2.34/1.00  comparisons_avoided:                    0
% 2.34/1.00  
% 2.34/1.00  ------ Simplifications
% 2.34/1.00  
% 2.34/1.00  
% 2.34/1.00  sim_fw_subset_subsumed:                 6
% 2.34/1.00  sim_bw_subset_subsumed:                 2
% 2.34/1.00  sim_fw_subsumed:                        0
% 2.34/1.00  sim_bw_subsumed:                        0
% 2.34/1.00  sim_fw_subsumption_res:                 0
% 2.34/1.00  sim_bw_subsumption_res:                 0
% 2.34/1.00  sim_tautology_del:                      6
% 2.34/1.00  sim_eq_tautology_del:                   0
% 2.34/1.00  sim_eq_res_simp:                        0
% 2.34/1.00  sim_fw_demodulated:                     1
% 2.34/1.00  sim_bw_demodulated:                     3
% 2.34/1.00  sim_light_normalised:                   11
% 2.34/1.00  sim_joinable_taut:                      0
% 2.34/1.00  sim_joinable_simp:                      0
% 2.34/1.00  sim_ac_normalised:                      0
% 2.34/1.00  sim_smt_subsumption:                    0
% 2.34/1.00  
%------------------------------------------------------------------------------
