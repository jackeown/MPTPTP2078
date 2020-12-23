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
% DateTime   : Thu Dec  3 12:24:15 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1588)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f24])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f28])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f29,f37,f36,f35,f34,f33,f32,f31,f30])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f38])).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
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

fof(f72,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
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

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f41,plain,(
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

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
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

fof(f76,plain,(
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
    inference(equality_resolution,[],[f75])).

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
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
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

fof(f74,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f70,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_768,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1277,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_323,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_324,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_328,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_25])).

cnf(c_329,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X2) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_758,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X2_56))))
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | u1_struct_0(X1_56) != u1_struct_0(sK0)
    | u1_struct_0(X2_56) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X2_56),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,X2_56,sK2,X0_56) ),
    inference(subtyping,[status(esa)],[c_329])).

cnf(c_1287,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK2,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,sK2,X2_56)
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_2250,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1287])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_784,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1580,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1753,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
    | v2_struct_0(X1_56)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X1_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,sK1,sK2,X0_56) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1754,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1753])).

cnf(c_2421,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2250,c_35,c_36,c_37,c_1580,c_1754])).

cnf(c_2422,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_2421])).

cnf(c_2434,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(sK0,sK1,sK2,X0_56)
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2422])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_766,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_570,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK2,X2) = k7_relat_1(sK2,X2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_754,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_1291,plain,
    ( k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2175,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) = k7_relat_1(sK2,X0_54) ),
    inference(superposition,[status(thm)],[c_1279,c_1291])).

cnf(c_2435,plain,
    ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2434,c_2175])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2466,plain,
    ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
    | m1_pre_topc(X0_56,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2435,c_32,c_33,c_34,c_40])).

cnf(c_2475,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_1277,c_2466])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_777,negated_conjecture,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1271,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_13,negated_conjecture,
    ( sK5 = sK7 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_776,negated_conjecture,
    ( sK5 = sK7 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_14,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_775,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1294,plain,
    ( sK6 = sK7 ),
    inference(light_normalisation,[status(thm)],[c_775,c_776])).

cnf(c_1338,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1271,c_776,c_1294])).

cnf(c_2618,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2475,c_1338])).

cnf(c_18,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_771,negated_conjecture,
    ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_7,plain,
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
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_496,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
    | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_497,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_501,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
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
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_25])).

cnf(c_502,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_501])).

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
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | u1_struct_0(X2_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_502])).

cnf(c_1290,plain,
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
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_2416,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1290])).

cnf(c_1581,plain,
    ( ~ r1_tmap_1(X0_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(X2_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X2_56),X0_53)
    | r1_tmap_1(k1_tsep_1(X1_56,X0_56,X2_56),sK1,k2_tmap_1(X1_56,sK1,sK2,k1_tsep_1(X1_56,X0_56,X2_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X2_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X1_56,X0_56,X2_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X1_56) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1590,plain,
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
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1581])).

cnf(c_2908,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2416,c_35,c_36,c_37])).

cnf(c_2909,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_2908])).

cnf(c_2929,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2909])).

cnf(c_4953,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_2929,c_32,c_33,c_34,c_40])).

cnf(c_4954,plain,
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
    inference(renaming,[status(thm)],[c_4953])).

cnf(c_4983,plain,
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
    inference(superposition,[status(thm)],[c_771,c_4954])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_770,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1275,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_2474,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_1275,c_2466])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_781,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X2_56,X1_56)
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1267,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X2_56,X1_56) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_1675,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) = iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_1267])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_44,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1975,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1675,c_32,c_34,c_41,c_42,c_43,c_44])).

cnf(c_2476,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1975,c_2466])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_0])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_2,c_1,c_0])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k7_relat_1(X0_53,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_1286,plain,
    ( k7_relat_1(X0_53,X0_54) = X0_53
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_2079,plain,
    ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_1279,c_1286])).

cnf(c_2493,plain,
    ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2476,c_2079])).

cnf(c_4996,plain,
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
    inference(light_normalisation,[status(thm)],[c_4983,c_771,c_2474,c_2475,c_2493])).

cnf(c_5361,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4996,c_41,c_42,c_43,c_44])).

cnf(c_5373,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2618,c_5361])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_368,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_369,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
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
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_25])).

cnf(c_374,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_757,plain,
    ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | u1_struct_0(X2_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1288,plain,
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
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_2337,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1288])).

cnf(c_2503,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2337,c_35,c_36,c_37,c_1580,c_1588])).

cnf(c_2504,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_2503])).

cnf(c_2523,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2504])).

cnf(c_3158,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2523,c_32,c_33,c_34,c_40])).

cnf(c_3159,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3158])).

cnf(c_3175,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) = iProver_top
    | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_3159])).

cnf(c_3185,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3175,c_771,c_2475,c_2493])).

cnf(c_3305,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
    | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3185,c_41,c_42,c_43,c_44])).

cnf(c_8,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_434,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_435,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_437,plain,
    ( ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
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
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_25])).

cnf(c_438,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK0)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_437])).

cnf(c_756,plain,
    ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
    | ~ r1_tmap_1(k1_tsep_1(X2_56,X3_56,X0_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X3_56,X0_56)),X0_53)
    | ~ m1_pre_topc(X0_56,X2_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X3_56,X0_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
    | v2_struct_0(X1_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | u1_struct_0(X2_56) != u1_struct_0(sK0)
    | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_1289,plain,
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
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_2360,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1289])).

cnf(c_2887,plain,
    ( l1_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK0)
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2360,c_35,c_36,c_37])).

cnf(c_2888,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK0)
    | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_2887])).

cnf(c_2905,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2888])).

cnf(c_3912,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_32,c_33,c_34,c_40])).

cnf(c_3913,plain,
    ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
    | m1_pre_topc(X0_56,sK0) != iProver_top
    | m1_pre_topc(X1_56,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_3912])).

cnf(c_3934,plain,
    ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_3913])).

cnf(c_3944,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3934,c_771,c_2474,c_2493])).

cnf(c_4068,plain,
    ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3944,c_41,c_42,c_43,c_44])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_779,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1269,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_1347,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1269,c_776,c_1294])).

cnf(c_2604,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_1347])).

cnf(c_2828,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2604,c_2475])).

cnf(c_4079,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4068,c_2828])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_47,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_773,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1273,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_1319,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1273,c_1294])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_772,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1274,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_1322,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1274,c_776])).

cnf(c_4329,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4079,c_47,c_1319,c_1322])).

cnf(c_4330,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
    | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4329])).

cnf(c_4336,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3305,c_4330])).

cnf(c_11,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_778,negated_conjecture,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1270,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_1333,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1270,c_776])).

cnf(c_2603,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
    | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2474,c_1333])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5373,c_4336,c_2603,c_1322,c_1319,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:38:23 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.33  % Running in FOF mode
% 3.20/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.98  
% 3.20/0.98  ------  iProver source info
% 3.20/0.98  
% 3.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.98  git: non_committed_changes: false
% 3.20/0.98  git: last_make_outside_of_git: false
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    --mode clausify
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.98  --prep_def_merge_mbd                    true
% 3.20/0.98  --prep_def_merge_tr_red                 false
% 3.20/0.98  --prep_def_merge_tr_cl                  false
% 3.20/0.98  --smt_preprocessing                     true
% 3.20/0.98  --smt_ac_axioms                         fast
% 3.20/0.98  --preprocessed_out                      false
% 3.20/0.98  --preprocessed_stats                    false
% 3.20/0.98  
% 3.20/0.98  ------ Abstraction refinement Options
% 3.20/0.98  
% 3.20/0.98  --abstr_ref                             []
% 3.20/0.98  --abstr_ref_prep                        false
% 3.20/0.98  --abstr_ref_until_sat                   false
% 3.20/0.98  --abstr_ref_sig_restrict                funpre
% 3.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.98  --abstr_ref_under                       []
% 3.20/0.98  
% 3.20/0.98  ------ SAT Options
% 3.20/0.98  
% 3.20/0.98  --sat_mode                              false
% 3.20/0.98  --sat_fm_restart_options                ""
% 3.20/0.98  --sat_gr_def                            false
% 3.20/0.98  --sat_epr_types                         true
% 3.20/0.98  --sat_non_cyclic_types                  false
% 3.20/0.98  --sat_finite_models                     false
% 3.20/0.98  --sat_fm_lemmas                         false
% 3.20/0.98  --sat_fm_prep                           false
% 3.20/0.98  --sat_fm_uc_incr                        true
% 3.20/0.98  --sat_out_model                         small
% 3.20/0.98  --sat_out_clauses                       false
% 3.20/0.98  
% 3.20/0.98  ------ QBF Options
% 3.20/0.98  
% 3.20/0.98  --qbf_mode                              false
% 3.20/0.98  --qbf_elim_univ                         false
% 3.20/0.98  --qbf_dom_inst                          none
% 3.20/0.98  --qbf_dom_pre_inst                      false
% 3.20/0.98  --qbf_sk_in                             false
% 3.20/0.98  --qbf_pred_elim                         true
% 3.20/0.98  --qbf_split                             512
% 3.20/0.98  
% 3.20/0.98  ------ BMC1 Options
% 3.20/0.98  
% 3.20/0.98  --bmc1_incremental                      false
% 3.20/0.98  --bmc1_axioms                           reachable_all
% 3.20/0.98  --bmc1_min_bound                        0
% 3.20/0.98  --bmc1_max_bound                        -1
% 3.20/0.98  --bmc1_max_bound_default                -1
% 3.20/0.98  --bmc1_symbol_reachability              true
% 3.20/0.98  --bmc1_property_lemmas                  false
% 3.20/0.98  --bmc1_k_induction                      false
% 3.20/0.98  --bmc1_non_equiv_states                 false
% 3.20/0.98  --bmc1_deadlock                         false
% 3.20/0.98  --bmc1_ucm                              false
% 3.20/0.98  --bmc1_add_unsat_core                   none
% 3.20/0.98  --bmc1_unsat_core_children              false
% 3.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.98  --bmc1_out_stat                         full
% 3.20/0.98  --bmc1_ground_init                      false
% 3.20/0.98  --bmc1_pre_inst_next_state              false
% 3.20/0.98  --bmc1_pre_inst_state                   false
% 3.20/0.98  --bmc1_pre_inst_reach_state             false
% 3.20/0.98  --bmc1_out_unsat_core                   false
% 3.20/0.98  --bmc1_aig_witness_out                  false
% 3.20/0.98  --bmc1_verbose                          false
% 3.20/0.98  --bmc1_dump_clauses_tptp                false
% 3.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.98  --bmc1_dump_file                        -
% 3.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.98  --bmc1_ucm_extend_mode                  1
% 3.20/0.98  --bmc1_ucm_init_mode                    2
% 3.20/0.98  --bmc1_ucm_cone_mode                    none
% 3.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.98  --bmc1_ucm_relax_model                  4
% 3.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.98  --bmc1_ucm_layered_model                none
% 3.20/0.98  --bmc1_ucm_max_lemma_size               10
% 3.20/0.98  
% 3.20/0.98  ------ AIG Options
% 3.20/0.98  
% 3.20/0.98  --aig_mode                              false
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation Options
% 3.20/0.98  
% 3.20/0.98  --instantiation_flag                    true
% 3.20/0.98  --inst_sos_flag                         false
% 3.20/0.98  --inst_sos_phase                        true
% 3.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel_side                     num_symb
% 3.20/0.98  --inst_solver_per_active                1400
% 3.20/0.98  --inst_solver_calls_frac                1.
% 3.20/0.98  --inst_passive_queue_type               priority_queues
% 3.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.98  --inst_passive_queues_freq              [25;2]
% 3.20/0.98  --inst_dismatching                      true
% 3.20/0.98  --inst_eager_unprocessed_to_passive     true
% 3.20/0.98  --inst_prop_sim_given                   true
% 3.20/0.98  --inst_prop_sim_new                     false
% 3.20/0.98  --inst_subs_new                         false
% 3.20/0.98  --inst_eq_res_simp                      false
% 3.20/0.98  --inst_subs_given                       false
% 3.20/0.98  --inst_orphan_elimination               true
% 3.20/0.98  --inst_learning_loop_flag               true
% 3.20/0.98  --inst_learning_start                   3000
% 3.20/0.98  --inst_learning_factor                  2
% 3.20/0.98  --inst_start_prop_sim_after_learn       3
% 3.20/0.98  --inst_sel_renew                        solver
% 3.20/0.98  --inst_lit_activity_flag                true
% 3.20/0.98  --inst_restr_to_given                   false
% 3.20/0.98  --inst_activity_threshold               500
% 3.20/0.98  --inst_out_proof                        true
% 3.20/0.98  
% 3.20/0.98  ------ Resolution Options
% 3.20/0.98  
% 3.20/0.98  --resolution_flag                       true
% 3.20/0.98  --res_lit_sel                           adaptive
% 3.20/0.98  --res_lit_sel_side                      none
% 3.20/0.98  --res_ordering                          kbo
% 3.20/0.98  --res_to_prop_solver                    active
% 3.20/0.98  --res_prop_simpl_new                    false
% 3.20/0.98  --res_prop_simpl_given                  true
% 3.20/0.98  --res_passive_queue_type                priority_queues
% 3.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.98  --res_passive_queues_freq               [15;5]
% 3.20/0.98  --res_forward_subs                      full
% 3.20/0.98  --res_backward_subs                     full
% 3.20/0.98  --res_forward_subs_resolution           true
% 3.20/0.98  --res_backward_subs_resolution          true
% 3.20/0.98  --res_orphan_elimination                true
% 3.20/0.98  --res_time_limit                        2.
% 3.20/0.98  --res_out_proof                         true
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Options
% 3.20/0.98  
% 3.20/0.98  --superposition_flag                    true
% 3.20/0.98  --sup_passive_queue_type                priority_queues
% 3.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.98  --demod_completeness_check              fast
% 3.20/0.98  --demod_use_ground                      true
% 3.20/0.98  --sup_to_prop_solver                    passive
% 3.20/0.98  --sup_prop_simpl_new                    true
% 3.20/0.98  --sup_prop_simpl_given                  true
% 3.20/0.98  --sup_fun_splitting                     false
% 3.20/0.98  --sup_smt_interval                      50000
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Simplification Setup
% 3.20/0.98  
% 3.20/0.98  --sup_indices_passive                   []
% 3.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_full_bw                           [BwDemod]
% 3.20/0.98  --sup_immed_triv                        [TrivRules]
% 3.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_immed_bw_main                     []
% 3.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  
% 3.20/0.98  ------ Combination Options
% 3.20/0.98  
% 3.20/0.98  --comb_res_mult                         3
% 3.20/0.98  --comb_sup_mult                         2
% 3.20/0.98  --comb_inst_mult                        10
% 3.20/0.98  
% 3.20/0.98  ------ Debug Options
% 3.20/0.98  
% 3.20/0.98  --dbg_backtrace                         false
% 3.20/0.98  --dbg_dump_prop_clauses                 false
% 3.20/0.98  --dbg_dump_prop_clauses_file            -
% 3.20/0.98  --dbg_out_stat                          false
% 3.20/0.98  ------ Parsing...
% 3.20/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.98  ------ Proving...
% 3.20/0.98  ------ Problem Properties 
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  clauses                                 28
% 3.20/0.98  conjectures                             20
% 3.20/0.98  EPR                                     12
% 3.20/0.98  Horn                                    20
% 3.20/0.98  unary                                   17
% 3.20/0.98  binary                                  4
% 3.20/0.98  lits                                    108
% 3.20/0.98  lits eq                                 14
% 3.20/0.98  fd_pure                                 0
% 3.20/0.98  fd_pseudo                               0
% 3.20/0.98  fd_cond                                 0
% 3.20/0.98  fd_pseudo_cond                          0
% 3.20/0.98  AC symbols                              0
% 3.20/0.98  
% 3.20/0.98  ------ Schedule dynamic 5 is on 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  Current options:
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    --mode clausify
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.98  --prep_def_merge_mbd                    true
% 3.20/0.98  --prep_def_merge_tr_red                 false
% 3.20/0.98  --prep_def_merge_tr_cl                  false
% 3.20/0.98  --smt_preprocessing                     true
% 3.20/0.98  --smt_ac_axioms                         fast
% 3.20/0.98  --preprocessed_out                      false
% 3.20/0.98  --preprocessed_stats                    false
% 3.20/0.98  
% 3.20/0.98  ------ Abstraction refinement Options
% 3.20/0.98  
% 3.20/0.98  --abstr_ref                             []
% 3.20/0.98  --abstr_ref_prep                        false
% 3.20/0.98  --abstr_ref_until_sat                   false
% 3.20/0.98  --abstr_ref_sig_restrict                funpre
% 3.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.98  --abstr_ref_under                       []
% 3.20/0.98  
% 3.20/0.98  ------ SAT Options
% 3.20/0.98  
% 3.20/0.98  --sat_mode                              false
% 3.20/0.98  --sat_fm_restart_options                ""
% 3.20/0.98  --sat_gr_def                            false
% 3.20/0.98  --sat_epr_types                         true
% 3.20/0.98  --sat_non_cyclic_types                  false
% 3.20/0.98  --sat_finite_models                     false
% 3.20/0.98  --sat_fm_lemmas                         false
% 3.20/0.98  --sat_fm_prep                           false
% 3.20/0.98  --sat_fm_uc_incr                        true
% 3.20/0.98  --sat_out_model                         small
% 3.20/0.98  --sat_out_clauses                       false
% 3.20/0.98  
% 3.20/0.98  ------ QBF Options
% 3.20/0.98  
% 3.20/0.98  --qbf_mode                              false
% 3.20/0.98  --qbf_elim_univ                         false
% 3.20/0.98  --qbf_dom_inst                          none
% 3.20/0.98  --qbf_dom_pre_inst                      false
% 3.20/0.98  --qbf_sk_in                             false
% 3.20/0.98  --qbf_pred_elim                         true
% 3.20/0.98  --qbf_split                             512
% 3.20/0.98  
% 3.20/0.98  ------ BMC1 Options
% 3.20/0.98  
% 3.20/0.98  --bmc1_incremental                      false
% 3.20/0.98  --bmc1_axioms                           reachable_all
% 3.20/0.98  --bmc1_min_bound                        0
% 3.20/0.98  --bmc1_max_bound                        -1
% 3.20/0.98  --bmc1_max_bound_default                -1
% 3.20/0.98  --bmc1_symbol_reachability              true
% 3.20/0.98  --bmc1_property_lemmas                  false
% 3.20/0.98  --bmc1_k_induction                      false
% 3.20/0.98  --bmc1_non_equiv_states                 false
% 3.20/0.98  --bmc1_deadlock                         false
% 3.20/0.98  --bmc1_ucm                              false
% 3.20/0.98  --bmc1_add_unsat_core                   none
% 3.20/0.98  --bmc1_unsat_core_children              false
% 3.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.98  --bmc1_out_stat                         full
% 3.20/0.98  --bmc1_ground_init                      false
% 3.20/0.98  --bmc1_pre_inst_next_state              false
% 3.20/0.98  --bmc1_pre_inst_state                   false
% 3.20/0.98  --bmc1_pre_inst_reach_state             false
% 3.20/0.98  --bmc1_out_unsat_core                   false
% 3.20/0.98  --bmc1_aig_witness_out                  false
% 3.20/0.98  --bmc1_verbose                          false
% 3.20/0.98  --bmc1_dump_clauses_tptp                false
% 3.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.98  --bmc1_dump_file                        -
% 3.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.98  --bmc1_ucm_extend_mode                  1
% 3.20/0.98  --bmc1_ucm_init_mode                    2
% 3.20/0.98  --bmc1_ucm_cone_mode                    none
% 3.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.98  --bmc1_ucm_relax_model                  4
% 3.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.98  --bmc1_ucm_layered_model                none
% 3.20/0.98  --bmc1_ucm_max_lemma_size               10
% 3.20/0.98  
% 3.20/0.98  ------ AIG Options
% 3.20/0.98  
% 3.20/0.98  --aig_mode                              false
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation Options
% 3.20/0.98  
% 3.20/0.98  --instantiation_flag                    true
% 3.20/0.98  --inst_sos_flag                         false
% 3.20/0.98  --inst_sos_phase                        true
% 3.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel_side                     none
% 3.20/0.98  --inst_solver_per_active                1400
% 3.20/0.98  --inst_solver_calls_frac                1.
% 3.20/0.98  --inst_passive_queue_type               priority_queues
% 3.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.98  --inst_passive_queues_freq              [25;2]
% 3.20/0.98  --inst_dismatching                      true
% 3.20/0.98  --inst_eager_unprocessed_to_passive     true
% 3.20/0.98  --inst_prop_sim_given                   true
% 3.20/0.98  --inst_prop_sim_new                     false
% 3.20/0.98  --inst_subs_new                         false
% 3.20/0.98  --inst_eq_res_simp                      false
% 3.20/0.98  --inst_subs_given                       false
% 3.20/0.98  --inst_orphan_elimination               true
% 3.20/0.98  --inst_learning_loop_flag               true
% 3.20/0.98  --inst_learning_start                   3000
% 3.20/0.98  --inst_learning_factor                  2
% 3.20/0.98  --inst_start_prop_sim_after_learn       3
% 3.20/0.98  --inst_sel_renew                        solver
% 3.20/0.98  --inst_lit_activity_flag                true
% 3.20/0.98  --inst_restr_to_given                   false
% 3.20/0.98  --inst_activity_threshold               500
% 3.20/0.98  --inst_out_proof                        true
% 3.20/0.98  
% 3.20/0.98  ------ Resolution Options
% 3.20/0.98  
% 3.20/0.98  --resolution_flag                       false
% 3.20/0.98  --res_lit_sel                           adaptive
% 3.20/0.98  --res_lit_sel_side                      none
% 3.20/0.98  --res_ordering                          kbo
% 3.20/0.98  --res_to_prop_solver                    active
% 3.20/0.98  --res_prop_simpl_new                    false
% 3.20/0.98  --res_prop_simpl_given                  true
% 3.20/0.98  --res_passive_queue_type                priority_queues
% 3.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.98  --res_passive_queues_freq               [15;5]
% 3.20/0.98  --res_forward_subs                      full
% 3.20/0.98  --res_backward_subs                     full
% 3.20/0.98  --res_forward_subs_resolution           true
% 3.20/0.98  --res_backward_subs_resolution          true
% 3.20/0.98  --res_orphan_elimination                true
% 3.20/0.98  --res_time_limit                        2.
% 3.20/0.98  --res_out_proof                         true
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Options
% 3.20/0.98  
% 3.20/0.98  --superposition_flag                    true
% 3.20/0.98  --sup_passive_queue_type                priority_queues
% 3.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.98  --demod_completeness_check              fast
% 3.20/0.98  --demod_use_ground                      true
% 3.20/0.98  --sup_to_prop_solver                    passive
% 3.20/0.98  --sup_prop_simpl_new                    true
% 3.20/0.98  --sup_prop_simpl_given                  true
% 3.20/0.98  --sup_fun_splitting                     false
% 3.20/0.98  --sup_smt_interval                      50000
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Simplification Setup
% 3.20/0.98  
% 3.20/0.98  --sup_indices_passive                   []
% 3.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_full_bw                           [BwDemod]
% 3.20/0.98  --sup_immed_triv                        [TrivRules]
% 3.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_immed_bw_main                     []
% 3.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  
% 3.20/0.98  ------ Combination Options
% 3.20/0.98  
% 3.20/0.98  --comb_res_mult                         3
% 3.20/0.98  --comb_sup_mult                         2
% 3.20/0.98  --comb_inst_mult                        10
% 3.20/0.98  
% 3.20/0.98  ------ Debug Options
% 3.20/0.98  
% 3.20/0.98  --dbg_backtrace                         false
% 3.20/0.98  --dbg_dump_prop_clauses                 false
% 3.20/0.98  --dbg_dump_prop_clauses_file            -
% 3.20/0.98  --dbg_out_stat                          false
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  ------ Proving...
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  % SZS status Theorem for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  fof(f8,conjecture,(
% 3.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f9,negated_conjecture,(
% 3.20/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 3.20/0.98    inference(negated_conjecture,[],[f8])).
% 3.20/0.98  
% 3.20/0.98  fof(f24,plain,(
% 3.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.20/0.98    inference(ennf_transformation,[],[f9])).
% 3.20/0.98  
% 3.20/0.98  fof(f25,plain,(
% 3.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.98    inference(flattening,[],[f24])).
% 3.20/0.98  
% 3.20/0.98  fof(f28,plain,(
% 3.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.98    inference(nnf_transformation,[],[f25])).
% 3.20/0.98  
% 3.20/0.98  fof(f29,plain,(
% 3.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.20/0.98    inference(flattening,[],[f28])).
% 3.20/0.98  
% 3.20/0.98  fof(f37,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK7 = X5 & X5 = X6 & m1_subset_1(sK7,u1_struct_0(X4)))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f36,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK6 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f35,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f34,plain,(
% 3.20/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK4) = X0 & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f33,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK3,X1,k2_tmap_1(X0,X1,X2,sK3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f32,plain,(
% 3.20/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6) | ~r1_tmap_1(X0,X1,sK2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK2,X3),X6)) | r1_tmap_1(X0,X1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f31,plain,(
% 3.20/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6) | ~r1_tmap_1(X0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(X0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(X0,sK1,X2,X3),X6)) | r1_tmap_1(X0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f30,plain,(
% 3.20/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & k1_tsep_1(sK0,X3,X4) = sK0 & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f38,plain,(
% 3.20/0.98    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & k1_tsep_1(sK0,sK3,sK4) = sK0 & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f29,f37,f36,f35,f34,f33,f32,f31,f30])).
% 3.20/0.98  
% 3.20/0.98  fof(f59,plain,(
% 3.20/0.98    m1_pre_topc(sK3,sK0)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f5,axiom,(
% 3.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f18,plain,(
% 3.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.98    inference(ennf_transformation,[],[f5])).
% 3.20/0.98  
% 3.20/0.98  fof(f19,plain,(
% 3.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.98    inference(flattening,[],[f18])).
% 3.20/0.98  
% 3.20/0.98  fof(f43,plain,(
% 3.20/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f19])).
% 3.20/0.98  
% 3.20/0.98  fof(f56,plain,(
% 3.20/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f55,plain,(
% 3.20/0.98    v1_funct_1(sK2)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f52,plain,(
% 3.20/0.98    ~v2_struct_0(sK1)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f53,plain,(
% 3.20/0.98    v2_pre_topc(sK1)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f54,plain,(
% 3.20/0.98    l1_pre_topc(sK1)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f57,plain,(
% 3.20/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f4,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f16,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.20/0.98    inference(ennf_transformation,[],[f4])).
% 3.20/0.98  
% 3.20/0.98  fof(f17,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.20/0.98    inference(flattening,[],[f16])).
% 3.20/0.98  
% 3.20/0.98  fof(f42,plain,(
% 3.20/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f17])).
% 3.20/0.98  
% 3.20/0.98  fof(f49,plain,(
% 3.20/0.98    ~v2_struct_0(sK0)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f50,plain,(
% 3.20/0.98    v2_pre_topc(sK0)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f51,plain,(
% 3.20/0.98    l1_pre_topc(sK0)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f68,plain,(
% 3.20/0.98    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f67,plain,(
% 3.20/0.98    sK5 = sK7),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f66,plain,(
% 3.20/0.98    sK5 = sK6),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f62,plain,(
% 3.20/0.98    k1_tsep_1(sK0,sK3,sK4) = sK0),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f7,axiom,(
% 3.20/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f22,plain,(
% 3.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.98    inference(ennf_transformation,[],[f7])).
% 3.20/0.98  
% 3.20/0.98  fof(f23,plain,(
% 3.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.98    inference(flattening,[],[f22])).
% 3.20/0.98  
% 3.20/0.98  fof(f26,plain,(
% 3.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.98    inference(nnf_transformation,[],[f23])).
% 3.20/0.98  
% 3.20/0.98  fof(f27,plain,(
% 3.20/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.98    inference(flattening,[],[f26])).
% 3.20/0.98  
% 3.20/0.98  fof(f48,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f27])).
% 3.20/0.98  
% 3.20/0.98  fof(f71,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f48])).
% 3.20/0.98  
% 3.20/0.98  fof(f72,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f71])).
% 3.20/0.98  
% 3.20/0.98  fof(f61,plain,(
% 3.20/0.98    m1_pre_topc(sK4,sK0)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f6,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f10,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.20/0.98    inference(pure_predicate_removal,[],[f6])).
% 3.20/0.98  
% 3.20/0.98  fof(f20,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.20/0.98    inference(ennf_transformation,[],[f10])).
% 3.20/0.98  
% 3.20/0.98  fof(f21,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.20/0.98    inference(flattening,[],[f20])).
% 3.20/0.98  
% 3.20/0.98  fof(f45,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f21])).
% 3.20/0.98  
% 3.20/0.98  fof(f58,plain,(
% 3.20/0.98    ~v2_struct_0(sK3)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f60,plain,(
% 3.20/0.98    ~v2_struct_0(sK4)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f3,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f11,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.20/0.98    inference(pure_predicate_removal,[],[f3])).
% 3.20/0.98  
% 3.20/0.98  fof(f15,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.98    inference(ennf_transformation,[],[f11])).
% 3.20/0.98  
% 3.20/0.98  fof(f41,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f15])).
% 3.20/0.98  
% 3.20/0.98  fof(f1,axiom,(
% 3.20/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f12,plain,(
% 3.20/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.20/0.98    inference(ennf_transformation,[],[f1])).
% 3.20/0.98  
% 3.20/0.98  fof(f13,plain,(
% 3.20/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/0.98    inference(flattening,[],[f12])).
% 3.20/0.98  
% 3.20/0.98  fof(f39,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f13])).
% 3.20/0.98  
% 3.20/0.98  fof(f2,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f14,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.98    inference(ennf_transformation,[],[f2])).
% 3.20/0.98  
% 3.20/0.98  fof(f40,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f14])).
% 3.20/0.98  
% 3.20/0.98  fof(f46,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f27])).
% 3.20/0.98  
% 3.20/0.98  fof(f75,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f46])).
% 3.20/0.98  
% 3.20/0.98  fof(f76,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f75])).
% 3.20/0.98  
% 3.20/0.98  fof(f47,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f27])).
% 3.20/0.98  
% 3.20/0.98  fof(f73,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f47])).
% 3.20/0.98  
% 3.20/0.98  fof(f74,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f73])).
% 3.20/0.98  
% 3.20/0.98  fof(f70,plain,(
% 3.20/0.98    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f65,plain,(
% 3.20/0.98    m1_subset_1(sK7,u1_struct_0(sK4))),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f64,plain,(
% 3.20/0.98    m1_subset_1(sK6,u1_struct_0(sK3))),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f63,plain,(
% 3.20/0.98    m1_subset_1(sK5,u1_struct_0(sK0))),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f69,plain,(
% 3.20/0.98    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  cnf(c_21,negated_conjecture,
% 3.20/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.20/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_768,negated_conjecture,
% 3.20/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.20/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1277,plain,
% 3.20/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_4,plain,
% 3.20/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.20/0.98      | ~ m1_pre_topc(X3,X1)
% 3.20/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.20/0.98      | v2_struct_0(X1)
% 3.20/0.98      | v2_struct_0(X2)
% 3.20/0.98      | ~ v2_pre_topc(X2)
% 3.20/0.98      | ~ v2_pre_topc(X1)
% 3.20/0.98      | ~ l1_pre_topc(X2)
% 3.20/0.98      | ~ l1_pre_topc(X1)
% 3.20/0.98      | ~ v1_funct_1(X0)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.20/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_24,negated_conjecture,
% 3.20/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.20/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_323,plain,
% 3.20/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.20/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.20/0.98      | v2_struct_0(X1)
% 3.20/0.98      | v2_struct_0(X3)
% 3.20/0.98      | ~ v2_pre_topc(X1)
% 3.20/0.98      | ~ v2_pre_topc(X3)
% 3.20/0.98      | ~ l1_pre_topc(X1)
% 3.20/0.98      | ~ l1_pre_topc(X3)
% 3.20/0.98      | ~ v1_funct_1(X2)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.20/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(X3) != u1_struct_0(sK1)
% 3.20/0.98      | sK2 != X2 ),
% 3.20/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_324,plain,
% 3.20/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.20/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.20/0.98      | v2_struct_0(X1)
% 3.20/0.98      | v2_struct_0(X2)
% 3.20/0.98      | ~ v2_pre_topc(X1)
% 3.20/0.98      | ~ v2_pre_topc(X2)
% 3.20/0.98      | ~ l1_pre_topc(X1)
% 3.20/0.98      | ~ l1_pre_topc(X2)
% 3.20/0.98      | ~ v1_funct_1(sK2)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 3.20/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.20/0.98      inference(unflattening,[status(thm)],[c_323]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_25,negated_conjecture,
% 3.20/0.98      ( v1_funct_1(sK2) ),
% 3.20/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_328,plain,
% 3.20/0.98      ( ~ l1_pre_topc(X2)
% 3.20/0.98      | ~ l1_pre_topc(X1)
% 3.20/0.98      | ~ v2_pre_topc(X2)
% 3.20/0.98      | ~ v2_pre_topc(X1)
% 3.20/0.98      | v2_struct_0(X2)
% 3.20/0.98      | v2_struct_0(X1)
% 3.20/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.20/0.98      | ~ m1_pre_topc(X0,X1)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 3.20/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.20/0.98      inference(global_propositional_subsumption,
% 3.20/0.98                [status(thm)],
% 3.20/0.98                [c_324,c_25]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_329,plain,
% 3.20/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.20/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.20/0.98      | v2_struct_0(X1)
% 3.20/0.98      | v2_struct_0(X2)
% 3.20/0.98      | ~ v2_pre_topc(X1)
% 3.20/0.98      | ~ v2_pre_topc(X2)
% 3.20/0.98      | ~ l1_pre_topc(X1)
% 3.20/0.98      | ~ l1_pre_topc(X2)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK2,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK2,X0)
% 3.20/0.98      | u1_struct_0(X1) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(X2) != u1_struct_0(sK1) ),
% 3.20/0.98      inference(renaming,[status(thm)],[c_328]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_758,plain,
% 3.20/0.98      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.20/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(X2_56))))
% 3.20/0.98      | v2_struct_0(X1_56)
% 3.20/0.98      | v2_struct_0(X2_56)
% 3.20/0.98      | ~ v2_pre_topc(X1_56)
% 3.20/0.98      | ~ v2_pre_topc(X2_56)
% 3.20/0.98      | ~ l1_pre_topc(X1_56)
% 3.20/0.98      | ~ l1_pre_topc(X2_56)
% 3.20/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(X2_56) != u1_struct_0(sK1)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(X2_56),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,X2_56,sK2,X0_56) ),
% 3.20/0.98      inference(subtyping,[status(esa)],[c_329]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1287,plain,
% 3.20/0.98      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),sK2,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,sK2,X2_56)
% 3.20/0.98      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.20/0.98      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.98      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.98      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | v2_pre_topc(X1_56) != iProver_top
% 3.20/0.98      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | l1_pre_topc(X1_56) != iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_2250,plain,
% 3.20/0.98      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 3.20/0.98      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.98      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.98      | v2_struct_0(sK1) = iProver_top
% 3.20/0.98      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.98      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.98      inference(equality_resolution,[status(thm)],[c_1287]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_28,negated_conjecture,
% 3.20/0.98      ( ~ v2_struct_0(sK1) ),
% 3.20/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_35,plain,
% 3.20/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_27,negated_conjecture,
% 3.20/0.98      ( v2_pre_topc(sK1) ),
% 3.20/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_36,plain,
% 3.20/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_26,negated_conjecture,
% 3.20/0.98      ( l1_pre_topc(sK1) ),
% 3.20/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_37,plain,
% 3.20/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_784,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1580,plain,
% 3.20/0.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.20/0.98      inference(instantiation,[status(thm)],[c_784]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1753,plain,
% 3.20/0.98      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.20/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
% 3.20/0.98      | v2_struct_0(X1_56)
% 3.20/0.98      | v2_struct_0(sK1)
% 3.20/0.98      | ~ v2_pre_topc(X1_56)
% 3.20/0.98      | ~ v2_pre_topc(sK1)
% 3.20/0.98      | ~ l1_pre_topc(X1_56)
% 3.20/0.98      | ~ l1_pre_topc(sK1)
% 3.20/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X1_56),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(X1_56,sK1,sK2,X0_56) ),
% 3.20/0.98      inference(instantiation,[status(thm)],[c_758]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1754,plain,
% 3.20/0.98      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 3.20/0.98      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.98      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.98      | v2_struct_0(sK1) = iProver_top
% 3.20/0.98      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.98      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_1753]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_2421,plain,
% 3.20/0.98      ( l1_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.98      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.98      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 3.20/0.98      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.98      | v2_pre_topc(X0_56) != iProver_top ),
% 3.20/0.98      inference(global_propositional_subsumption,
% 3.20/0.98                [status(thm)],
% 3.20/0.98                [c_2250,c_35,c_36,c_37,c_1580,c_1754]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_2422,plain,
% 3.20/0.98      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.98      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(sK1),sK2,u1_struct_0(X1_56)) = k2_tmap_1(X0_56,sK1,sK2,X1_56)
% 3.20/0.98      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.98      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.98      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.98      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.98      inference(renaming,[status(thm)],[c_2421]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_2434,plain,
% 3.20/0.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0_56)) = k2_tmap_1(sK0,sK1,sK2,X0_56)
% 3.20/0.98      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.98      | v2_struct_0(sK0) = iProver_top
% 3.20/0.98      | v2_pre_topc(sK0) != iProver_top
% 3.20/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.20/0.98      inference(equality_resolution,[status(thm)],[c_2422]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_23,negated_conjecture,
% 3.20/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.20/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_766,negated_conjecture,
% 3.20/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.20/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1279,plain,
% 3.20/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_3,plain,
% 3.20/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.98      | ~ v1_funct_1(X0)
% 3.20/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.20/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_569,plain,
% 3.20/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.20/0.99      | sK2 != X0 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_570,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | k2_partfun1(X0,X1,sK2,X2) = k7_relat_1(sK2,X2) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_569]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_754,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.20/0.99      | k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_570]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1291,plain,
% 3.20/0.99      ( k2_partfun1(X0_54,X1_54,sK2,X2_54) = k7_relat_1(sK2,X2_54)
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2175,plain,
% 3.20/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_54) = k7_relat_1(sK2,X0_54) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1279,c_1291]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2435,plain,
% 3.20/0.99      ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(sK0) = iProver_top
% 3.20/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2434,c_2175]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_31,negated_conjecture,
% 3.20/0.99      ( ~ v2_struct_0(sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_32,plain,
% 3.20/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_30,negated_conjecture,
% 3.20/0.99      ( v2_pre_topc(sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_33,plain,
% 3.20/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_29,negated_conjecture,
% 3.20/0.99      ( l1_pre_topc(sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_34,plain,
% 3.20/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_40,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2466,plain,
% 3.20/0.99      ( k2_tmap_1(sK0,sK1,sK2,X0_56) = k7_relat_1(sK2,u1_struct_0(X0_56))
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2435,c_32,c_33,c_34,c_40]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2475,plain,
% 3.20/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1277,c_2466]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_12,negated_conjecture,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 3.20/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_777,negated_conjecture,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1271,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_13,negated_conjecture,
% 3.20/0.99      ( sK5 = sK7 ),
% 3.20/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_776,negated_conjecture,
% 3.20/0.99      ( sK5 = sK7 ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_14,negated_conjecture,
% 3.20/0.99      ( sK5 = sK6 ),
% 3.20/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_775,negated_conjecture,
% 3.20/0.99      ( sK5 = sK6 ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1294,plain,
% 3.20/0.99      ( sK6 = sK7 ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_775,c_776]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1338,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1271,c_776,c_1294]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2618,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2475,c_1338]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_18,negated_conjecture,
% 3.20/0.99      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_771,negated_conjecture,
% 3.20/0.99      ( k1_tsep_1(sK0,sK3,sK4) = sK0 ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7,plain,
% 3.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 3.20/0.99      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 3.20/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 3.20/0.99      | ~ m1_pre_topc(X5,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X5)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(X3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_496,plain,
% 3.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 3.20/0.99      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 3.20/0.99      | ~ m1_pre_topc(X5,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X5)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.20/0.99      | sK2 != X3 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_497,plain,
% 3.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_501,plain,
% 3.20/0.99      ( ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 3.20/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 3.20/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_497,c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_502,plain,
% 3.20/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK2,X4),X3)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_501]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_755,plain,
% 3.20/0.99      ( ~ r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
% 3.20/0.99      | ~ r1_tmap_1(X3_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X3_56),X0_53)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
% 3.20/0.99      | ~ m1_pre_topc(X0_56,X2_56)
% 3.20/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 3.20/0.99      | v2_struct_0(X1_56)
% 3.20/0.99      | v2_struct_0(X0_56)
% 3.20/0.99      | v2_struct_0(X2_56)
% 3.20/0.99      | v2_struct_0(X3_56)
% 3.20/0.99      | ~ v2_pre_topc(X1_56)
% 3.20/0.99      | ~ v2_pre_topc(X2_56)
% 3.20/0.99      | ~ l1_pre_topc(X1_56)
% 3.20/0.99      | ~ l1_pre_topc(X2_56)
% 3.20/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_502]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1290,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 3.20/0.99      | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X3_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X3_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X3_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X2_56,X3_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X3_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X3_56) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2416,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_1290]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1581,plain,
% 3.20/0.99      ( ~ r1_tmap_1(X0_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X0_56),X0_53)
% 3.20/0.99      | ~ r1_tmap_1(X2_56,sK1,k2_tmap_1(X1_56,sK1,sK2,X2_56),X0_53)
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X1_56,X0_56,X2_56),sK1,k2_tmap_1(X1_56,sK1,sK2,k1_tsep_1(X1_56,X0_56,X2_56)),X0_53)
% 3.20/0.99      | ~ m1_pre_topc(X0_56,X1_56)
% 3.20/0.99      | ~ m1_pre_topc(X2_56,X1_56)
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X2_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X1_56,X0_56,X2_56)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_56),u1_struct_0(sK1))))
% 3.20/0.99      | v2_struct_0(X1_56)
% 3.20/0.99      | v2_struct_0(X0_56)
% 3.20/0.99      | v2_struct_0(X2_56)
% 3.20/0.99      | v2_struct_0(sK1)
% 3.20/0.99      | ~ v2_pre_topc(X1_56)
% 3.20/0.99      | ~ v2_pre_topc(sK1)
% 3.20/0.99      | ~ l1_pre_topc(X1_56)
% 3.20/0.99      | ~ l1_pre_topc(sK1)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_755]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1590,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1581]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2908,plain,
% 3.20/0.99      ( l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2416,c_35,c_36,c_37]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2909,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X2_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X2_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_2908]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2929,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK0) = iProver_top
% 3.20/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_2909]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4953,plain,
% 3.20/0.99      ( v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2929,c_32,c_33,c_34,c_40]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4954,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(sK0,sK1,sK2,X1_56),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_4953]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4983,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_771,c_4954]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_19,negated_conjecture,
% 3.20/0.99      ( m1_pre_topc(sK4,sK0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_770,negated_conjecture,
% 3.20/0.99      ( m1_pre_topc(sK4,sK0) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1275,plain,
% 3.20/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2474,plain,
% 3.20/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1275,c_2466]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5,plain,
% 3.20/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.20/0.99      | ~ m1_pre_topc(X2,X1)
% 3.20/0.99      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | ~ l1_pre_topc(X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_781,plain,
% 3.20/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 3.20/0.99      | ~ m1_pre_topc(X2_56,X1_56)
% 3.20/0.99      | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56)
% 3.20/0.99      | v2_struct_0(X1_56)
% 3.20/0.99      | v2_struct_0(X0_56)
% 3.20/0.99      | v2_struct_0(X2_56)
% 3.20/0.99      | ~ l1_pre_topc(X1_56) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1267,plain,
% 3.20/0.99      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X1_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(k1_tsep_1(X1_56,X2_56,X0_56),X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | l1_pre_topc(X1_56) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1675,plain,
% 3.20/0.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK0,sK0) = iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK0) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top
% 3.20/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_771,c_1267]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_22,negated_conjecture,
% 3.20/0.99      ( ~ v2_struct_0(sK3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_41,plain,
% 3.20/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_42,plain,
% 3.20/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_20,negated_conjecture,
% 3.20/0.99      ( ~ v2_struct_0(sK4) ),
% 3.20/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_43,plain,
% 3.20/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_44,plain,
% 3.20/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1975,plain,
% 3.20/0.99      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1675,c_32,c_34,c_41,c_42,c_43,c_44]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2476,plain,
% 3.20/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0)) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1975,c_2466]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | v4_relat_1(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_0,plain,
% 3.20/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_303,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.20/0.99      inference(resolution,[status(thm)],[c_2,c_0]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_307,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_303,c_2,c_1,c_0]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_759,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.20/0.99      | k7_relat_1(X0_53,X0_54) = X0_53 ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_307]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1286,plain,
% 3.20/0.99      ( k7_relat_1(X0_53,X0_54) = X0_53
% 3.20/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2079,plain,
% 3.20/0.99      ( k7_relat_1(sK2,u1_struct_0(sK0)) = sK2 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1279,c_1286]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2493,plain,
% 3.20/0.99      ( k2_tmap_1(sK0,sK1,sK2,sK0) = sK2 ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_2476,c_2079]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4996,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4983,c_771,c_2474,c_2475,c_2493]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5361,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4996,c_41,c_42,c_43,c_44]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5373,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2618,c_5361]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 3.20/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X5,X2)
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X5)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(X3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_368,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 3.20/0.99      | ~ m1_pre_topc(X5,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X5)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.20/0.99      | sK2 != X3 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_369,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_373,plain,
% 3.20/0.99      ( ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 3.20/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_369,c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_374,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X0,X4)),X3)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_373]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_757,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_56,X0_56,X3_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X0_56,X3_56)),X0_53)
% 3.20/0.99      | ~ m1_pre_topc(X0_56,X2_56)
% 3.20/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X0_56,X3_56)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 3.20/0.99      | v2_struct_0(X1_56)
% 3.20/0.99      | v2_struct_0(X0_56)
% 3.20/0.99      | v2_struct_0(X2_56)
% 3.20/0.99      | v2_struct_0(X3_56)
% 3.20/0.99      | ~ v2_pre_topc(X1_56)
% 3.20/0.99      | ~ v2_pre_topc(X2_56)
% 3.20/0.99      | ~ l1_pre_topc(X1_56)
% 3.20/0.99      | ~ l1_pre_topc(X2_56)
% 3.20/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_374]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1288,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 3.20/0.99      | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X3_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X2_56,X3_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X3_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X3_56) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2337,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_1288]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2503,plain,
% 3.20/0.99      ( l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 3.20/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2337,c_35,c_36,c_37,c_1580,c_1588]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2504,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X1_56,X2_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X1_56,X2_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X1_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_2503]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2523,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK0) = iProver_top
% 3.20/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_2504]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3158,plain,
% 3.20/0.99      ( v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2523,c_32,c_33,c_34,c_40]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3159,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X0_56,X1_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X0_56,X1_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X0_56,X1_56))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_3158]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3175,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_771,c_3159]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3185,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3175,c_771,c_2475,c_2493]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3305,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3185,c_41,c_42,c_43,c_44]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 3.20/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 3.20/0.99      | ~ m1_pre_topc(X5,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X5)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(X3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_434,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 3.20/0.99      | ~ m1_pre_topc(X5,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 3.20/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X5)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.20/0.99      | sK2 != X3 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_435,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_437,plain,
% 3.20/0.99      ( ~ l1_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 3.20/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_435,c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_438,plain,
% 3.20/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X4,X0),X1,k2_tmap_1(X2,X1,sK2,k1_tsep_1(X2,X4,X0)),X3)
% 3.20/0.99      | ~ m1_pre_topc(X0,X2)
% 3.20/0.99      | ~ m1_pre_topc(X4,X2)
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.20/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X4,X0)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.20/0.99      | v2_struct_0(X1)
% 3.20/0.99      | v2_struct_0(X0)
% 3.20/0.99      | v2_struct_0(X2)
% 3.20/0.99      | v2_struct_0(X4)
% 3.20/0.99      | ~ v2_pre_topc(X1)
% 3.20/0.99      | ~ v2_pre_topc(X2)
% 3.20/0.99      | ~ l1_pre_topc(X1)
% 3.20/0.99      | ~ l1_pre_topc(X2)
% 3.20/0.99      | u1_struct_0(X2) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_437]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_756,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,X1_56,k2_tmap_1(X2_56,X1_56,sK2,X0_56),X0_53)
% 3.20/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_56,X3_56,X0_56),X1_56,k2_tmap_1(X2_56,X1_56,sK2,k1_tsep_1(X2_56,X3_56,X0_56)),X0_53)
% 3.20/0.99      | ~ m1_pre_topc(X0_56,X2_56)
% 3.20/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_56))
% 3.20/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_56,X3_56,X0_56)))
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_56),u1_struct_0(X1_56))))
% 3.20/0.99      | v2_struct_0(X1_56)
% 3.20/0.99      | v2_struct_0(X0_56)
% 3.20/0.99      | v2_struct_0(X2_56)
% 3.20/0.99      | v2_struct_0(X3_56)
% 3.20/0.99      | ~ v2_pre_topc(X1_56)
% 3.20/0.99      | ~ v2_pre_topc(X2_56)
% 3.20/0.99      | ~ l1_pre_topc(X1_56)
% 3.20/0.99      | ~ l1_pre_topc(X2_56)
% 3.20/0.99      | u1_struct_0(X2_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_438]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1289,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK1)
% 3.20/0.99      | r1_tmap_1(X2_56,X1_56,k2_tmap_1(X0_56,X1_56,sK2,X2_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X3_56,X2_56),X1_56,k2_tmap_1(X0_56,X1_56,sK2,k1_tsep_1(X0_56,X3_56,X2_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X3_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X3_56,X2_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X3_56) = iProver_top
% 3.20/0.99      | v2_pre_topc(X1_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X1_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2360,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK1) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_1289]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2887,plain,
% 3.20/0.99      ( l1_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 3.20/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2360,c_35,c_36,c_37]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2888,plain,
% 3.20/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK0)
% 3.20/0.99      | r1_tmap_1(X1_56,sK1,k2_tmap_1(X0_56,sK1,sK2,X1_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(X0_56,X2_56,X1_56),sK1,k2_tmap_1(X0_56,sK1,sK2,k1_tsep_1(X0_56,X2_56,X1_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_56,X2_56,X1_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X2_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_pre_topc(X0_56) != iProver_top
% 3.20/0.99      | l1_pre_topc(X0_56) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_2887]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2905,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(sK0) = iProver_top
% 3.20/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.20/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_2888]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3912,plain,
% 3.20/0.99      ( v2_struct_0(X0_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2905,c_32,c_33,c_34,c_40]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3913,plain,
% 3.20/0.99      ( r1_tmap_1(X0_56,sK1,k2_tmap_1(sK0,sK1,sK2,X0_56),X0_53) = iProver_top
% 3.20/0.99      | r1_tmap_1(k1_tsep_1(sK0,X1_56,X0_56),sK1,k2_tmap_1(sK0,sK1,sK2,k1_tsep_1(sK0,X1_56,X0_56)),X0_53) != iProver_top
% 3.20/0.99      | m1_pre_topc(X0_56,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(X1_56,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_56)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,X1_56,X0_56))) != iProver_top
% 3.20/0.99      | v2_struct_0(X1_56) = iProver_top
% 3.20/0.99      | v2_struct_0(X0_56) = iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_3912]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3934,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK0,sK3,sK4))) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_771,c_3913]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3944,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
% 3.20/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.20/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 3.20/0.99      | v2_struct_0(sK3) = iProver_top
% 3.20/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3934,c_771,c_2474,c_2493]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4068,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,X0_53) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0_53) = iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3944,c_41,c_42,c_43,c_44]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10,negated_conjecture,
% 3.20/0.99      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.20/0.99      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.20/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_779,negated_conjecture,
% 3.20/0.99      ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
% 3.20/0.99      | ~ r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.20/0.99      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1269,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK5) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1347,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1269,c_776,c_1294]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2604,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2474,c_1347]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2828,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_2604,c_2475]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4079,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4068,c_2828]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_15,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_47,plain,
% 3.20/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_16,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_773,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1273,plain,
% 3.20/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1319,plain,
% 3.20/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1273,c_1294]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_17,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_772,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK5,u1_struct_0(sK0)) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1274,plain,
% 3.20/0.99      ( m1_subset_1(sK5,u1_struct_0(sK0)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1322,plain,
% 3.20/0.99      ( m1_subset_1(sK7,u1_struct_0(sK0)) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1274,c_776]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4329,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4079,c_47,c_1319,c_1322]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4330,plain,
% 3.20/0.99      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK7) != iProver_top
% 3.20/0.99      | r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_4329]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4336,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK0)) != iProver_top
% 3.20/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3305,c_4330]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_11,negated_conjecture,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_778,negated_conjecture,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK5)
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
% 3.20/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1270,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK5) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1333,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) = iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1270,c_776]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2603,plain,
% 3.20/0.99      ( r1_tmap_1(sK0,sK1,sK2,sK7) = iProver_top
% 3.20/0.99      | r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK7) = iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2474,c_1333]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(contradiction,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(minisat,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5373,c_4336,c_2603,c_1322,c_1319,c_47]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ General
% 3.20/0.99  
% 3.20/0.99  abstr_ref_over_cycles:                  0
% 3.20/0.99  abstr_ref_under_cycles:                 0
% 3.20/0.99  gc_basic_clause_elim:                   0
% 3.20/0.99  forced_gc_time:                         0
% 3.20/0.99  parsing_time:                           0.006
% 3.20/0.99  unif_index_cands_time:                  0.
% 3.20/0.99  unif_index_add_time:                    0.
% 3.20/0.99  orderings_time:                         0.
% 3.20/0.99  out_proof_time:                         0.018
% 3.20/0.99  total_time:                             0.222
% 3.20/0.99  num_of_symbols:                         57
% 3.20/0.99  num_of_terms:                           3611
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing
% 3.20/0.99  
% 3.20/0.99  num_of_splits:                          0
% 3.20/0.99  num_of_split_atoms:                     0
% 3.20/0.99  num_of_reused_defs:                     0
% 3.20/0.99  num_eq_ax_congr_red:                    8
% 3.20/0.99  num_of_sem_filtered_clauses:            1
% 3.20/0.99  num_of_subtypes:                        4
% 3.20/0.99  monotx_restored_types:                  0
% 3.20/0.99  sat_num_of_epr_types:                   0
% 3.20/0.99  sat_num_of_non_cyclic_types:            0
% 3.20/0.99  sat_guarded_non_collapsed_types:        1
% 3.20/0.99  num_pure_diseq_elim:                    0
% 3.20/0.99  simp_replaced_by:                       0
% 3.20/0.99  res_preprocessed:                       157
% 3.20/0.99  prep_upred:                             0
% 3.20/0.99  prep_unflattend:                        5
% 3.20/0.99  smt_new_axioms:                         0
% 3.20/0.99  pred_elim_cands:                        6
% 3.20/0.99  pred_elim:                              4
% 3.20/0.99  pred_elim_cl:                           4
% 3.20/0.99  pred_elim_cycles:                       6
% 3.20/0.99  merged_defs:                            0
% 3.20/0.99  merged_defs_ncl:                        0
% 3.20/0.99  bin_hyper_res:                          0
% 3.20/0.99  prep_cycles:                            4
% 3.20/0.99  pred_elim_time:                         0.012
% 3.20/0.99  splitting_time:                         0.
% 3.20/0.99  sem_filter_time:                        0.
% 3.20/0.99  monotx_time:                            0.
% 3.20/0.99  subtype_inf_time:                       0.001
% 3.20/0.99  
% 3.20/0.99  ------ Problem properties
% 3.20/0.99  
% 3.20/0.99  clauses:                                28
% 3.20/0.99  conjectures:                            20
% 3.20/0.99  epr:                                    12
% 3.20/0.99  horn:                                   20
% 3.20/0.99  ground:                                 20
% 3.20/0.99  unary:                                  17
% 3.20/0.99  binary:                                 4
% 3.20/0.99  lits:                                   108
% 3.20/0.99  lits_eq:                                14
% 3.20/0.99  fd_pure:                                0
% 3.20/0.99  fd_pseudo:                              0
% 3.20/0.99  fd_cond:                                0
% 3.20/0.99  fd_pseudo_cond:                         0
% 3.20/0.99  ac_symbols:                             0
% 3.20/0.99  
% 3.20/0.99  ------ Propositional Solver
% 3.20/0.99  
% 3.20/0.99  prop_solver_calls:                      29
% 3.20/0.99  prop_fast_solver_calls:                 1768
% 3.20/0.99  smt_solver_calls:                       0
% 3.20/0.99  smt_fast_solver_calls:                  0
% 3.20/0.99  prop_num_of_clauses:                    1422
% 3.20/0.99  prop_preprocess_simplified:             4756
% 3.20/0.99  prop_fo_subsumed:                       85
% 3.20/0.99  prop_solver_time:                       0.
% 3.20/0.99  smt_solver_time:                        0.
% 3.20/0.99  smt_fast_solver_time:                   0.
% 3.20/0.99  prop_fast_solver_time:                  0.
% 3.20/0.99  prop_unsat_core_time:                   0.
% 3.20/0.99  
% 3.20/0.99  ------ QBF
% 3.20/0.99  
% 3.20/0.99  qbf_q_res:                              0
% 3.20/0.99  qbf_num_tautologies:                    0
% 3.20/0.99  qbf_prep_cycles:                        0
% 3.20/0.99  
% 3.20/0.99  ------ BMC1
% 3.20/0.99  
% 3.20/0.99  bmc1_current_bound:                     -1
% 3.20/0.99  bmc1_last_solved_bound:                 -1
% 3.20/0.99  bmc1_unsat_core_size:                   -1
% 3.20/0.99  bmc1_unsat_core_parents_size:           -1
% 3.20/0.99  bmc1_merge_next_fun:                    0
% 3.20/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation
% 3.20/0.99  
% 3.20/0.99  inst_num_of_clauses:                    415
% 3.20/0.99  inst_num_in_passive:                    68
% 3.20/0.99  inst_num_in_active:                     340
% 3.20/0.99  inst_num_in_unprocessed:                7
% 3.20/0.99  inst_num_of_loops:                      370
% 3.20/0.99  inst_num_of_learning_restarts:          0
% 3.20/0.99  inst_num_moves_active_passive:          25
% 3.20/0.99  inst_lit_activity:                      0
% 3.20/0.99  inst_lit_activity_moves:                0
% 3.20/0.99  inst_num_tautologies:                   0
% 3.20/0.99  inst_num_prop_implied:                  0
% 3.20/0.99  inst_num_existing_simplified:           0
% 3.20/0.99  inst_num_eq_res_simplified:             0
% 3.20/0.99  inst_num_child_elim:                    0
% 3.20/0.99  inst_num_of_dismatching_blockings:      161
% 3.20/0.99  inst_num_of_non_proper_insts:           579
% 3.20/0.99  inst_num_of_duplicates:                 0
% 3.20/0.99  inst_inst_num_from_inst_to_res:         0
% 3.20/0.99  inst_dismatching_checking_time:         0.
% 3.20/0.99  
% 3.20/0.99  ------ Resolution
% 3.20/0.99  
% 3.20/0.99  res_num_of_clauses:                     0
% 3.20/0.99  res_num_in_passive:                     0
% 3.20/0.99  res_num_in_active:                      0
% 3.20/0.99  res_num_of_loops:                       161
% 3.20/0.99  res_forward_subset_subsumed:            125
% 3.20/0.99  res_backward_subset_subsumed:           0
% 3.20/0.99  res_forward_subsumed:                   0
% 3.20/0.99  res_backward_subsumed:                  0
% 3.20/0.99  res_forward_subsumption_resolution:     0
% 3.20/0.99  res_backward_subsumption_resolution:    0
% 3.20/0.99  res_clause_to_clause_subsumption:       453
% 3.20/0.99  res_orphan_elimination:                 0
% 3.20/0.99  res_tautology_del:                      75
% 3.20/0.99  res_num_eq_res_simplified:              0
% 3.20/0.99  res_num_sel_changes:                    0
% 3.20/0.99  res_moves_from_active_to_pass:          0
% 3.20/0.99  
% 3.20/0.99  ------ Superposition
% 3.20/0.99  
% 3.20/0.99  sup_time_total:                         0.
% 3.20/0.99  sup_time_generating:                    0.
% 3.20/0.99  sup_time_sim_full:                      0.
% 3.20/0.99  sup_time_sim_immed:                     0.
% 3.20/0.99  
% 3.20/0.99  sup_num_of_clauses:                     111
% 3.20/0.99  sup_num_in_active:                      68
% 3.20/0.99  sup_num_in_passive:                     43
% 3.20/0.99  sup_num_of_loops:                       72
% 3.20/0.99  sup_fw_superposition:                   70
% 3.20/0.99  sup_bw_superposition:                   22
% 3.20/0.99  sup_immediate_simplified:               46
% 3.20/0.99  sup_given_eliminated:                   0
% 3.20/0.99  comparisons_done:                       0
% 3.20/0.99  comparisons_avoided:                    0
% 3.20/0.99  
% 3.20/0.99  ------ Simplifications
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  sim_fw_subset_subsumed:                 1
% 3.20/0.99  sim_bw_subset_subsumed:                 3
% 3.20/0.99  sim_fw_subsumed:                        0
% 3.20/0.99  sim_bw_subsumed:                        0
% 3.20/0.99  sim_fw_subsumption_res:                 0
% 3.20/0.99  sim_bw_subsumption_res:                 1
% 3.20/0.99  sim_tautology_del:                      6
% 3.20/0.99  sim_eq_tautology_del:                   3
% 3.20/0.99  sim_eq_res_simp:                        0
% 3.20/0.99  sim_fw_demodulated:                     1
% 3.20/0.99  sim_bw_demodulated:                     3
% 3.20/0.99  sim_light_normalised:                   50
% 3.20/0.99  sim_joinable_taut:                      0
% 3.20/0.99  sim_joinable_simp:                      0
% 3.20/0.99  sim_ac_normalised:                      0
% 3.20/0.99  sim_smt_subsumption:                    0
% 3.20/0.99  
%------------------------------------------------------------------------------
