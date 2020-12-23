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
% DateTime   : Thu Dec  3 12:24:17 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1847)

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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(flattening,[],[f33])).

fof(f42,plain,(
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
     => ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
          | ~ r1_tmap_1(X0,X1,X2,X5) )
        & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK8)
            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
          | r1_tmap_1(X0,X1,X2,X5) )
        & sK8 = X5
        & X5 = X6
        & m1_subset_1(sK8,u1_struct_0(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK7)
              | ~ r1_tmap_1(X0,X1,X2,X5) )
            & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK7) )
              | r1_tmap_1(X0,X1,X2,X5) )
            & X5 = X7
            & sK7 = X5
            & m1_subset_1(X7,u1_struct_0(X4)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                  | ~ r1_tmap_1(X0,X1,X2,sK6) )
                & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                    & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                  | r1_tmap_1(X0,X1,X2,sK6) )
                & sK6 = X7
                & sK6 = X6
                & m1_subset_1(X7,u1_struct_0(X4)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                    ( ( ~ r1_tmap_1(sK5,X1,k2_tmap_1(X0,X1,X2,sK5),X7)
                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                    & ( ( r1_tmap_1(sK5,X1,k2_tmap_1(X0,X1,X2,sK5),X7)
                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                      | r1_tmap_1(X0,X1,X2,X5) )
                    & X5 = X7
                    & X5 = X6
                    & m1_subset_1(X7,u1_struct_0(sK5)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & k1_tsep_1(X0,X3,sK5) = X0
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
                          | ~ r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X6)
                          | ~ r1_tmap_1(X0,X1,X2,X5) )
                        & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                            & r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X6) )
                          | r1_tmap_1(X0,X1,X2,X5) )
                        & X5 = X7
                        & X5 = X6
                        & m1_subset_1(X7,u1_struct_0(X4)) )
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & k1_tsep_1(X0,sK4,X4) = X0
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
                            ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK3,X4),X7)
                              | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK3,X3),X6)
                              | ~ r1_tmap_1(X0,X1,sK3,X5) )
                            & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK3,X4),X7)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK3,X3),X6) )
                              | r1_tmap_1(X0,X1,sK3,X5) )
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
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                                ( ( ~ r1_tmap_1(X4,sK2,k2_tmap_1(X0,sK2,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK2,k2_tmap_1(X0,sK2,X2,X3),X6)
                                  | ~ r1_tmap_1(X0,sK2,X2,X5) )
                                & ( ( r1_tmap_1(X4,sK2,k2_tmap_1(X0,sK2,X2,X4),X7)
                                    & r1_tmap_1(X3,sK2,k2_tmap_1(X0,sK2,X2,X3),X6) )
                                  | r1_tmap_1(X0,sK2,X2,X5) )
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
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK1,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(sK1,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK1,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X6) )
                                    | r1_tmap_1(sK1,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(sK1)) )
                      & k1_tsep_1(sK1,X3,X4) = sK1
                      & m1_pre_topc(X4,sK1)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8)
      | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
      | ~ r1_tmap_1(sK1,sK2,sK3,sK6) )
    & ( ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8)
        & r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) )
      | r1_tmap_1(sK1,sK2,sK3,sK6) )
    & sK6 = sK8
    & sK6 = sK7
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK1))
    & k1_tsep_1(sK1,sK4,sK5) = sK1
    & m1_pre_topc(sK5,sK1)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f34,f42,f41,f40,f39,f38,f37,f36,f35])).

fof(f74,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
    | r1_tmap_1(sK1,sK2,sK3,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    sK6 = sK8 ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    k1_tsep_1(sK1,sK4,sK5) = sK1 ),
    inference(cnf_transformation,[],[f43])).

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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f50])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f62,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    m1_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(equality_resolution,[],[f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f48])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8)
    | r1_tmap_1(sK1,sK2,sK3,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8)
    | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
    | ~ r1_tmap_1(sK1,sK2,sK3,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
    | r1_tmap_1(sK1,sK2,sK3,sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1017,negated_conjecture,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
    | r1_tmap_1(sK1,sK2,sK3,sK6) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1503,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_14,negated_conjecture,
    ( sK6 = sK8 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1016,negated_conjecture,
    ( sK6 = sK8 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_15,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1015,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1526,plain,
    ( sK7 = sK8 ),
    inference(light_normalisation,[status(thm)],[c_1015,c_1016])).

cnf(c_1570,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK8) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1503,c_1016,c_1526])).

cnf(c_19,negated_conjecture,
    ( k1_tsep_1(sK1,sK4,sK5) = sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1011,negated_conjecture,
    ( k1_tsep_1(sK1,sK4,sK5) = sK1 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_4,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
    | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_753,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
    | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_754,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK3,X4),X3)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK3,X4),X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_754,c_26])).

cnf(c_759,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK3,X4),X3)
    | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_758])).

cnf(c_994,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
    | ~ r1_tmap_1(X3_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X3_52),X0_53)
    | r1_tmap_1(k1_tsep_1(X2_52,X0_52,X3_52),X1_52,k2_tmap_1(X2_52,X1_52,sK3,k1_tsep_1(X2_52,X0_52,X3_52)),X0_53)
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_52,X0_52,X3_52)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X3_52)
    | u1_struct_0(X2_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_759])).

cnf(c_1523,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2)
    | r1_tmap_1(X2_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X2_52),X0_53) != iProver_top
    | r1_tmap_1(X3_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X3_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X2_52,X3_52),X1_52,k2_tmap_1(X0_52,X1_52,sK3,k1_tsep_1(X0_52,X2_52,X3_52)),X0_53) = iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X3_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X3_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X2_52,X3_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_2851,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
    | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1523])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1025,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1833,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_1835,plain,
    ( ~ r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),X0_53)
    | ~ r1_tmap_1(X2_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X2_52),X0_53)
    | r1_tmap_1(k1_tsep_1(X1_52,X0_52,X2_52),sK2,k2_tmap_1(X1_52,sK2,sK3,k1_tsep_1(X1_52,X0_52,X2_52)),X0_53)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X2_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X1_52,X0_52,X2_52)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK2)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_1849,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
    | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1835])).

cnf(c_3375,plain,
    ( v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
    | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2851,c_36,c_37,c_38])).

cnf(c_3376,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
    | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_3375])).

cnf(c_3396,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(sK1,sK2,sK3,X1_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) = iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3376])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3895,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(sK1,sK2,sK3,X1_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) = iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3396,c_33,c_34,c_35,c_41])).

cnf(c_3896,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(sK1,sK2,sK3,X1_52),X0_53) != iProver_top
    | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) = iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_3895])).

cnf(c_3911,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) != iProver_top
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK5,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,sK4,sK5))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_3896])).

cnf(c_3952,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) != iProver_top
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK5,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3911,c_1011])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_42,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_44,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_45,plain,
    ( m1_pre_topc(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4032,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) != iProver_top
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3952,c_42,c_43,c_44,c_45])).

cnf(c_4044,plain,
    ( r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),sK8) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_4032])).

cnf(c_10,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_161,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_162,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_519,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_25])).

cnf(c_520,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_26])).

cnf(c_525,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_560,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_525,c_1])).

cnf(c_997,plain,
    ( r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
    | ~ r1_tmap_1(X2_52,X1_52,sK3,X0_53)
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | u1_struct_0(X2_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_1520,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2)
    | r1_tmap_1(X2_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X2_52),X0_53) = iProver_top
    | r1_tmap_1(X0_52,X1_52,sK3,X0_53) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_2986,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1520])).

cnf(c_1834,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),X0_53)
    | ~ r1_tmap_1(X1_52,sK2,sK3,X0_53)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK2)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1853,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(c_3080,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_36,c_37,c_38])).

cnf(c_3081,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_3080])).

cnf(c_3096,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3081])).

cnf(c_3180,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3096,c_33,c_34,c_35,c_41])).

cnf(c_3181,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_3180])).

cnf(c_6,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_625,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X5,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_626,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_630,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_26])).

cnf(c_631,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_630])).

cnf(c_996,plain,
    ( r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
    | ~ r1_tmap_1(k1_tsep_1(X2_52,X0_52,X3_52),X1_52,k2_tmap_1(X2_52,X1_52,sK3,k1_tsep_1(X2_52,X0_52,X3_52)),X0_53)
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_52,X0_52,X3_52)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X3_52)
    | u1_struct_0(X2_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_631])).

cnf(c_1521,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2)
    | r1_tmap_1(X2_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X2_52),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X2_52,X3_52),X1_52,k2_tmap_1(X0_52,X1_52,sK3,k1_tsep_1(X0_52,X2_52,X3_52)),X0_53) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X3_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X3_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X2_52,X3_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_2752,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1521])).

cnf(c_3274,plain,
    ( v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) != iProver_top
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2752,c_36,c_37,c_38,c_1833,c_1847])).

cnf(c_3275,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_3274])).

cnf(c_3294,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3275])).

cnf(c_3542,plain,
    ( v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3294,c_33,c_34,c_35,c_41])).

cnf(c_3543,plain,
    ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
    | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_3542])).

cnf(c_3558,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK5,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,sK4,sK5))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_3543])).

cnf(c_3569,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK5,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3558,c_1011])).

cnf(c_3709,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3569,c_42,c_43,c_44,c_45])).

cnf(c_3720,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_3709])).

cnf(c_7,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_61,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_63,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_3829,plain,
    ( m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_33,c_35,c_63])).

cnf(c_3830,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3829])).

cnf(c_4046,plain,
    ( r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
    | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3830,c_4032])).

cnf(c_4065,plain,
    ( r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),sK8) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4044,c_4046])).

cnf(c_12,negated_conjecture,
    ( r1_tmap_1(sK1,sK2,sK3,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1018,negated_conjecture,
    ( r1_tmap_1(sK1,sK2,sK3,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1502,plain,
    ( r1_tmap_1(sK1,sK2,sK3,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_1565,plain,
    ( r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1502,c_1016])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_48,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1031,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(X1_52)
    | X0_52 != X1_52 ),
    theory(equality)).

cnf(c_1042,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1023,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1052,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_2358,plain,
    ( ~ r1_tmap_1(X0_52,sK2,sK3,sK8)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(X0_52,sK2,sK3,sK5),sK8)
    | ~ m1_pre_topc(sK5,X0_52)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | v2_struct_0(sK5)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2359,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(X0_52,sK2,sK3,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(X0_52,sK2,sK3,sK5),sK8) = iProver_top
    | m1_pre_topc(sK5,X0_52) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2358])).

cnf(c_2361,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top
    | m1_pre_topc(sK5,sK1) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_2417,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1565,c_33,c_34,c_35,c_36,c_37,c_38,c_41,c_44,c_45,c_48,c_1042,c_1052,c_1833,c_2361])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
    | ~ r1_tmap_1(sK1,sK2,sK3,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1019,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
    | ~ r1_tmap_1(sK1,sK2,sK3,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1501,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) != iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_1575,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK8) != iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1501,c_1016,c_1526])).

cnf(c_2422,plain,
    ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK8) != iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_1575])).

cnf(c_3191,plain,
    ( r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_2422])).

cnf(c_3,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_317,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | X5 != X6
    | u1_struct_0(X4) != X7 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_318,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_358,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_318,c_1])).

cnf(c_399,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | X0 != X6
    | X3 != X5
    | sK0(X6,X5) != X7 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_358])).

cnf(c_400,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_2,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | X3 != X1
    | X2 != X0
    | sK0(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_421,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_400,c_379])).

cnf(c_438,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_1])).

cnf(c_462,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_438,c_25])).

cnf(c_463,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_467,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK0(X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_26])).

cnf(c_468,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK0(X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_467])).

cnf(c_998,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
    | r1_tmap_1(X2_52,X1_52,sK3,X0_53)
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK0(X2_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | u1_struct_0(X2_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_1838,plain,
    ( ~ r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),X0_53)
    | r1_tmap_1(X1_52,sK2,sK3,X0_53)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK0(X1_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK2)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_2255,plain,
    ( ~ r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),sK8)
    | r1_tmap_1(X1_52,sK2,sK3,sK8)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(sK0(X1_52,sK8),k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK8,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK2)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_2256,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),sK8) != iProver_top
    | r1_tmap_1(X0_52,sK2,sK3,sK8) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(sK0(X0_52,sK8),k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2255])).

cnf(c_2258,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),sK8) != iProver_top
    | r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(sK0(sK1,sK8),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2256])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | m1_subset_1(sK0(X0_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X0_52)
    | v2_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_1986,plain,
    ( m1_subset_1(sK0(X0_52,sK8),k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK8,u1_struct_0(X0_52))
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X0_52)
    | v2_struct_0(X0_52) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_1987,plain,
    ( m1_subset_1(sK0(X0_52,sK8),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(X0_52)) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1986])).

cnf(c_1989,plain,
    ( m1_subset_1(sK0(sK1,sK8),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1012,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1506,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_1554,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1506,c_1016])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1013,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1505,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_1551,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1505,c_1526])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4065,c_3191,c_2417,c_2258,c_1989,c_1833,c_1554,c_1551,c_1052,c_1042,c_63,c_48,c_43,c_42,c_41,c_38,c_37,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:49:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.44/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.99  
% 2.44/0.99  ------  iProver source info
% 2.44/0.99  
% 2.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.99  git: non_committed_changes: false
% 2.44/0.99  git: last_make_outside_of_git: false
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/0.99  --sat_fm_uc_incr                        true
% 2.44/0.99  --sat_out_model                         small
% 2.44/0.99  --sat_out_clauses                       false
% 2.44/0.99  
% 2.44/0.99  ------ QBF Options
% 2.44/0.99  
% 2.44/0.99  --qbf_mode                              false
% 2.44/0.99  --qbf_elim_univ                         false
% 2.44/0.99  --qbf_dom_inst                          none
% 2.44/0.99  --qbf_dom_pre_inst                      false
% 2.44/0.99  --qbf_sk_in                             false
% 2.44/0.99  --qbf_pred_elim                         true
% 2.44/0.99  --qbf_split                             512
% 2.44/0.99  
% 2.44/0.99  ------ BMC1 Options
% 2.44/0.99  
% 2.44/0.99  --bmc1_incremental                      false
% 2.44/0.99  --bmc1_axioms                           reachable_all
% 2.44/0.99  --bmc1_min_bound                        0
% 2.44/0.99  --bmc1_max_bound                        -1
% 2.44/0.99  --bmc1_max_bound_default                -1
% 2.44/0.99  --bmc1_symbol_reachability              true
% 2.44/0.99  --bmc1_property_lemmas                  false
% 2.44/0.99  --bmc1_k_induction                      false
% 2.44/0.99  --bmc1_non_equiv_states                 false
% 2.44/0.99  --bmc1_deadlock                         false
% 2.44/0.99  --bmc1_ucm                              false
% 2.44/0.99  --bmc1_add_unsat_core                   none
% 2.44/0.99  --bmc1_unsat_core_children              false
% 2.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.99  --bmc1_out_stat                         full
% 2.44/0.99  --bmc1_ground_init                      false
% 2.44/0.99  --bmc1_pre_inst_next_state              false
% 2.44/0.99  --bmc1_pre_inst_state                   false
% 2.44/0.99  --bmc1_pre_inst_reach_state             false
% 2.44/0.99  --bmc1_out_unsat_core                   false
% 2.44/0.99  --bmc1_aig_witness_out                  false
% 2.44/0.99  --bmc1_verbose                          false
% 2.44/0.99  --bmc1_dump_clauses_tptp                false
% 2.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.99  --bmc1_dump_file                        -
% 2.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.99  --bmc1_ucm_extend_mode                  1
% 2.44/0.99  --bmc1_ucm_init_mode                    2
% 2.44/0.99  --bmc1_ucm_cone_mode                    none
% 2.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.99  --bmc1_ucm_relax_model                  4
% 2.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.99  --bmc1_ucm_layered_model                none
% 2.44/0.99  --bmc1_ucm_max_lemma_size               10
% 2.44/0.99  
% 2.44/0.99  ------ AIG Options
% 2.44/0.99  
% 2.44/0.99  --aig_mode                              false
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation Options
% 2.44/0.99  
% 2.44/0.99  --instantiation_flag                    true
% 2.44/0.99  --inst_sos_flag                         false
% 2.44/0.99  --inst_sos_phase                        true
% 2.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel_side                     num_symb
% 2.44/0.99  --inst_solver_per_active                1400
% 2.44/0.99  --inst_solver_calls_frac                1.
% 2.44/0.99  --inst_passive_queue_type               priority_queues
% 2.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.99  --inst_passive_queues_freq              [25;2]
% 2.44/0.99  --inst_dismatching                      true
% 2.44/0.99  --inst_eager_unprocessed_to_passive     true
% 2.44/0.99  --inst_prop_sim_given                   true
% 2.44/0.99  --inst_prop_sim_new                     false
% 2.44/0.99  --inst_subs_new                         false
% 2.44/0.99  --inst_eq_res_simp                      false
% 2.44/0.99  --inst_subs_given                       false
% 2.44/0.99  --inst_orphan_elimination               true
% 2.44/0.99  --inst_learning_loop_flag               true
% 2.44/0.99  --inst_learning_start                   3000
% 2.44/0.99  --inst_learning_factor                  2
% 2.44/0.99  --inst_start_prop_sim_after_learn       3
% 2.44/0.99  --inst_sel_renew                        solver
% 2.44/0.99  --inst_lit_activity_flag                true
% 2.44/0.99  --inst_restr_to_given                   false
% 2.44/0.99  --inst_activity_threshold               500
% 2.44/0.99  --inst_out_proof                        true
% 2.44/0.99  
% 2.44/0.99  ------ Resolution Options
% 2.44/0.99  
% 2.44/0.99  --resolution_flag                       true
% 2.44/0.99  --res_lit_sel                           adaptive
% 2.44/0.99  --res_lit_sel_side                      none
% 2.44/0.99  --res_ordering                          kbo
% 2.44/0.99  --res_to_prop_solver                    active
% 2.44/0.99  --res_prop_simpl_new                    false
% 2.44/0.99  --res_prop_simpl_given                  true
% 2.44/0.99  --res_passive_queue_type                priority_queues
% 2.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.99  --res_passive_queues_freq               [15;5]
% 2.44/0.99  --res_forward_subs                      full
% 2.44/0.99  --res_backward_subs                     full
% 2.44/0.99  --res_forward_subs_resolution           true
% 2.44/0.99  --res_backward_subs_resolution          true
% 2.44/0.99  --res_orphan_elimination                true
% 2.44/0.99  --res_time_limit                        2.
% 2.44/0.99  --res_out_proof                         true
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Options
% 2.44/0.99  
% 2.44/0.99  --superposition_flag                    true
% 2.44/0.99  --sup_passive_queue_type                priority_queues
% 2.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.99  --demod_completeness_check              fast
% 2.44/0.99  --demod_use_ground                      true
% 2.44/0.99  --sup_to_prop_solver                    passive
% 2.44/0.99  --sup_prop_simpl_new                    true
% 2.44/0.99  --sup_prop_simpl_given                  true
% 2.44/0.99  --sup_fun_splitting                     false
% 2.44/0.99  --sup_smt_interval                      50000
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Simplification Setup
% 2.44/0.99  
% 2.44/0.99  --sup_indices_passive                   []
% 2.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_full_bw                           [BwDemod]
% 2.44/0.99  --sup_immed_triv                        [TrivRules]
% 2.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_immed_bw_main                     []
% 2.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  
% 2.44/0.99  ------ Combination Options
% 2.44/0.99  
% 2.44/0.99  --comb_res_mult                         3
% 2.44/0.99  --comb_sup_mult                         2
% 2.44/0.99  --comb_inst_mult                        10
% 2.44/0.99  
% 2.44/0.99  ------ Debug Options
% 2.44/0.99  
% 2.44/0.99  --dbg_backtrace                         false
% 2.44/0.99  --dbg_dump_prop_clauses                 false
% 2.44/0.99  --dbg_dump_prop_clauses_file            -
% 2.44/0.99  --dbg_out_stat                          false
% 2.44/0.99  ------ Parsing...
% 2.44/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.99  ------ Proving...
% 2.44/0.99  ------ Problem Properties 
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  clauses                                 28
% 2.44/0.99  conjectures                             20
% 2.44/0.99  EPR                                     13
% 2.44/0.99  Horn                                    19
% 2.44/0.99  unary                                   17
% 2.44/0.99  binary                                  3
% 2.44/0.99  lits                                    121
% 2.44/0.99  lits eq                                 13
% 2.44/0.99  fd_pure                                 0
% 2.44/0.99  fd_pseudo                               0
% 2.44/0.99  fd_cond                                 0
% 2.44/0.99  fd_pseudo_cond                          0
% 2.44/0.99  AC symbols                              0
% 2.44/0.99  
% 2.44/0.99  ------ Schedule dynamic 5 is on 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  Current options:
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/0.99  --sat_fm_uc_incr                        true
% 2.44/0.99  --sat_out_model                         small
% 2.44/0.99  --sat_out_clauses                       false
% 2.44/0.99  
% 2.44/0.99  ------ QBF Options
% 2.44/0.99  
% 2.44/0.99  --qbf_mode                              false
% 2.44/0.99  --qbf_elim_univ                         false
% 2.44/0.99  --qbf_dom_inst                          none
% 2.44/0.99  --qbf_dom_pre_inst                      false
% 2.44/0.99  --qbf_sk_in                             false
% 2.44/0.99  --qbf_pred_elim                         true
% 2.44/0.99  --qbf_split                             512
% 2.44/0.99  
% 2.44/0.99  ------ BMC1 Options
% 2.44/0.99  
% 2.44/0.99  --bmc1_incremental                      false
% 2.44/0.99  --bmc1_axioms                           reachable_all
% 2.44/0.99  --bmc1_min_bound                        0
% 2.44/0.99  --bmc1_max_bound                        -1
% 2.44/0.99  --bmc1_max_bound_default                -1
% 2.44/0.99  --bmc1_symbol_reachability              true
% 2.44/0.99  --bmc1_property_lemmas                  false
% 2.44/0.99  --bmc1_k_induction                      false
% 2.44/0.99  --bmc1_non_equiv_states                 false
% 2.44/0.99  --bmc1_deadlock                         false
% 2.44/0.99  --bmc1_ucm                              false
% 2.44/0.99  --bmc1_add_unsat_core                   none
% 2.44/0.99  --bmc1_unsat_core_children              false
% 2.44/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.99  --bmc1_out_stat                         full
% 2.44/0.99  --bmc1_ground_init                      false
% 2.44/0.99  --bmc1_pre_inst_next_state              false
% 2.44/0.99  --bmc1_pre_inst_state                   false
% 2.44/0.99  --bmc1_pre_inst_reach_state             false
% 2.44/0.99  --bmc1_out_unsat_core                   false
% 2.44/0.99  --bmc1_aig_witness_out                  false
% 2.44/0.99  --bmc1_verbose                          false
% 2.44/0.99  --bmc1_dump_clauses_tptp                false
% 2.44/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.99  --bmc1_dump_file                        -
% 2.44/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.99  --bmc1_ucm_extend_mode                  1
% 2.44/0.99  --bmc1_ucm_init_mode                    2
% 2.44/0.99  --bmc1_ucm_cone_mode                    none
% 2.44/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.99  --bmc1_ucm_relax_model                  4
% 2.44/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.99  --bmc1_ucm_layered_model                none
% 2.44/0.99  --bmc1_ucm_max_lemma_size               10
% 2.44/0.99  
% 2.44/0.99  ------ AIG Options
% 2.44/0.99  
% 2.44/0.99  --aig_mode                              false
% 2.44/0.99  
% 2.44/0.99  ------ Instantiation Options
% 2.44/0.99  
% 2.44/0.99  --instantiation_flag                    true
% 2.44/0.99  --inst_sos_flag                         false
% 2.44/0.99  --inst_sos_phase                        true
% 2.44/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.99  --inst_lit_sel_side                     none
% 2.44/0.99  --inst_solver_per_active                1400
% 2.44/0.99  --inst_solver_calls_frac                1.
% 2.44/0.99  --inst_passive_queue_type               priority_queues
% 2.44/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.99  --inst_passive_queues_freq              [25;2]
% 2.44/0.99  --inst_dismatching                      true
% 2.44/0.99  --inst_eager_unprocessed_to_passive     true
% 2.44/0.99  --inst_prop_sim_given                   true
% 2.44/0.99  --inst_prop_sim_new                     false
% 2.44/0.99  --inst_subs_new                         false
% 2.44/0.99  --inst_eq_res_simp                      false
% 2.44/0.99  --inst_subs_given                       false
% 2.44/0.99  --inst_orphan_elimination               true
% 2.44/0.99  --inst_learning_loop_flag               true
% 2.44/0.99  --inst_learning_start                   3000
% 2.44/0.99  --inst_learning_factor                  2
% 2.44/0.99  --inst_start_prop_sim_after_learn       3
% 2.44/0.99  --inst_sel_renew                        solver
% 2.44/0.99  --inst_lit_activity_flag                true
% 2.44/0.99  --inst_restr_to_given                   false
% 2.44/0.99  --inst_activity_threshold               500
% 2.44/0.99  --inst_out_proof                        true
% 2.44/0.99  
% 2.44/0.99  ------ Resolution Options
% 2.44/0.99  
% 2.44/0.99  --resolution_flag                       false
% 2.44/0.99  --res_lit_sel                           adaptive
% 2.44/0.99  --res_lit_sel_side                      none
% 2.44/0.99  --res_ordering                          kbo
% 2.44/0.99  --res_to_prop_solver                    active
% 2.44/0.99  --res_prop_simpl_new                    false
% 2.44/0.99  --res_prop_simpl_given                  true
% 2.44/0.99  --res_passive_queue_type                priority_queues
% 2.44/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.99  --res_passive_queues_freq               [15;5]
% 2.44/0.99  --res_forward_subs                      full
% 2.44/0.99  --res_backward_subs                     full
% 2.44/0.99  --res_forward_subs_resolution           true
% 2.44/0.99  --res_backward_subs_resolution          true
% 2.44/0.99  --res_orphan_elimination                true
% 2.44/0.99  --res_time_limit                        2.
% 2.44/0.99  --res_out_proof                         true
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Options
% 2.44/0.99  
% 2.44/0.99  --superposition_flag                    true
% 2.44/0.99  --sup_passive_queue_type                priority_queues
% 2.44/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.99  --demod_completeness_check              fast
% 2.44/0.99  --demod_use_ground                      true
% 2.44/0.99  --sup_to_prop_solver                    passive
% 2.44/0.99  --sup_prop_simpl_new                    true
% 2.44/0.99  --sup_prop_simpl_given                  true
% 2.44/0.99  --sup_fun_splitting                     false
% 2.44/0.99  --sup_smt_interval                      50000
% 2.44/0.99  
% 2.44/0.99  ------ Superposition Simplification Setup
% 2.44/0.99  
% 2.44/0.99  --sup_indices_passive                   []
% 2.44/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_full_bw                           [BwDemod]
% 2.44/0.99  --sup_immed_triv                        [TrivRules]
% 2.44/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_immed_bw_main                     []
% 2.44/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.99  
% 2.44/0.99  ------ Combination Options
% 2.44/0.99  
% 2.44/0.99  --comb_res_mult                         3
% 2.44/0.99  --comb_sup_mult                         2
% 2.44/0.99  --comb_inst_mult                        10
% 2.44/0.99  
% 2.44/0.99  ------ Debug Options
% 2.44/0.99  
% 2.44/0.99  --dbg_backtrace                         false
% 2.44/0.99  --dbg_dump_prop_clauses                 false
% 2.44/0.99  --dbg_dump_prop_clauses_file            -
% 2.44/0.99  --dbg_out_stat                          false
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  ------ Proving...
% 2.44/0.99  
% 2.44/0.99  
% 2.44/0.99  % SZS status Theorem for theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  fof(f9,conjecture,(
% 2.44/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f10,negated_conjecture,(
% 2.44/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 2.44/0.99    inference(negated_conjecture,[],[f9])).
% 2.44/0.99  
% 2.44/0.99  fof(f26,plain,(
% 2.44/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f10])).
% 2.44/0.99  
% 2.44/0.99  fof(f27,plain,(
% 2.44/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f26])).
% 2.44/0.99  
% 2.44/0.99  fof(f33,plain,(
% 2.44/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/0.99    inference(nnf_transformation,[],[f27])).
% 2.44/0.99  
% 2.44/0.99  fof(f34,plain,(
% 2.44/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f33])).
% 2.44/0.99  
% 2.44/0.99  fof(f42,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) => ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK8) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),sK8) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & sK8 = X5 & X5 = X6 & m1_subset_1(sK8,u1_struct_0(X4)))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f41,plain,(
% 2.44/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK7) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),sK7)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & sK7 = X5 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f40,plain,(
% 2.44/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,sK6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,sK6)) & sK6 = X7 & sK6 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f39,plain,(
% 2.44/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK5,X1,k2_tmap_1(X0,X1,X2,sK5),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(sK5,X1,k2_tmap_1(X0,X1,X2,sK5),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK5))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,sK5) = X0 & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f38,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(sK4,X1,k2_tmap_1(X0,X1,X2,sK4),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,sK4,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f37,plain,(
% 2.44/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK3,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK3,X3),X6) | ~r1_tmap_1(X0,X1,sK3,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK3,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,sK3,X3),X6)) | r1_tmap_1(X0,X1,sK3,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f36,plain,(
% 2.44/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK2,k2_tmap_1(X0,sK2,X2,X4),X7) | ~r1_tmap_1(X3,sK2,k2_tmap_1(X0,sK2,X2,X3),X6) | ~r1_tmap_1(X0,sK2,X2,X5)) & ((r1_tmap_1(X4,sK2,k2_tmap_1(X0,sK2,X2,X4),X7) & r1_tmap_1(X3,sK2,k2_tmap_1(X0,sK2,X2,X3),X6)) | r1_tmap_1(X0,sK2,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f35,plain,(
% 2.44/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK1,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X6) | ~r1_tmap_1(sK1,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK1,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK1,X1,X2,X3),X6)) | r1_tmap_1(sK1,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & k1_tsep_1(sK1,X3,X4) = sK1 & m1_pre_topc(X4,sK1) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f43,plain,(
% 2.44/0.99    ((((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) | ~r1_tmap_1(sK1,sK2,sK3,sK6)) & ((r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) & r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)) | r1_tmap_1(sK1,sK2,sK3,sK6)) & sK6 = sK8 & sK6 = sK7 & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK1))) & k1_tsep_1(sK1,sK4,sK5) = sK1 & m1_pre_topc(sK5,sK1) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f34,f42,f41,f40,f39,f38,f37,f36,f35])).
% 2.44/0.99  
% 2.44/0.99  fof(f74,plain,(
% 2.44/0.99    r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) | r1_tmap_1(sK1,sK2,sK3,sK6)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f73,plain,(
% 2.44/0.99    sK6 = sK8),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f72,plain,(
% 2.44/0.99    sK6 = sK7),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f68,plain,(
% 2.44/0.99    k1_tsep_1(sK1,sK4,sK5) = sK1),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f5,axiom,(
% 2.44/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f19,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f5])).
% 2.44/0.99  
% 2.44/0.99  fof(f20,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f19])).
% 2.44/0.99  
% 2.44/0.99  fof(f30,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(nnf_transformation,[],[f20])).
% 2.44/0.99  
% 2.44/0.99  fof(f31,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f30])).
% 2.44/0.99  
% 2.44/0.99  fof(f50,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f31])).
% 2.44/0.99  
% 2.44/0.99  fof(f77,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f50])).
% 2.44/0.99  
% 2.44/0.99  fof(f78,plain,(
% 2.44/0.99    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f77])).
% 2.44/0.99  
% 2.44/0.99  fof(f62,plain,(
% 2.44/0.99    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f61,plain,(
% 2.44/0.99    v1_funct_1(sK3)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f58,plain,(
% 2.44/0.99    ~v2_struct_0(sK2)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f59,plain,(
% 2.44/0.99    v2_pre_topc(sK2)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f60,plain,(
% 2.44/0.99    l1_pre_topc(sK2)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f55,plain,(
% 2.44/0.99    ~v2_struct_0(sK1)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f56,plain,(
% 2.44/0.99    v2_pre_topc(sK1)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f57,plain,(
% 2.44/0.99    l1_pre_topc(sK1)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f63,plain,(
% 2.44/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f64,plain,(
% 2.44/0.99    ~v2_struct_0(sK4)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f65,plain,(
% 2.44/0.99    m1_pre_topc(sK4,sK1)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f66,plain,(
% 2.44/0.99    ~v2_struct_0(sK5)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f67,plain,(
% 2.44/0.99    m1_pre_topc(sK5,sK1)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f8,axiom,(
% 2.44/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f24,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f8])).
% 2.44/0.99  
% 2.44/0.99  fof(f25,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f24])).
% 2.44/0.99  
% 2.44/0.99  fof(f32,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(nnf_transformation,[],[f25])).
% 2.44/0.99  
% 2.44/0.99  fof(f53,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f32])).
% 2.44/0.99  
% 2.44/0.99  fof(f85,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f53])).
% 2.44/0.99  
% 2.44/0.99  fof(f7,axiom,(
% 2.44/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f22,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f7])).
% 2.44/0.99  
% 2.44/0.99  fof(f23,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f22])).
% 2.44/0.99  
% 2.44/0.99  fof(f52,plain,(
% 2.44/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f23])).
% 2.44/0.99  
% 2.44/0.99  fof(f83,plain,(
% 2.44/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f52])).
% 2.44/0.99  
% 2.44/0.99  fof(f2,axiom,(
% 2.44/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f13,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f2])).
% 2.44/0.99  
% 2.44/0.99  fof(f14,plain,(
% 2.44/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f13])).
% 2.44/0.99  
% 2.44/0.99  fof(f45,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f14])).
% 2.44/0.99  
% 2.44/0.99  fof(f48,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f31])).
% 2.44/0.99  
% 2.44/0.99  fof(f81,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f48])).
% 2.44/0.99  
% 2.44/0.99  fof(f82,plain,(
% 2.44/0.99    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f81])).
% 2.44/0.99  
% 2.44/0.99  fof(f6,axiom,(
% 2.44/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f21,plain,(
% 2.44/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.44/0.99    inference(ennf_transformation,[],[f6])).
% 2.44/0.99  
% 2.44/0.99  fof(f51,plain,(
% 2.44/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f21])).
% 2.44/0.99  
% 2.44/0.99  fof(f75,plain,(
% 2.44/0.99    r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) | r1_tmap_1(sK1,sK2,sK3,sK6)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f71,plain,(
% 2.44/0.99    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f76,plain,(
% 2.44/0.99    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) | ~r1_tmap_1(sK1,sK2,sK3,sK6)),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f4,axiom,(
% 2.44/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f17,plain,(
% 2.44/0.99    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f4])).
% 2.44/0.99  
% 2.44/0.99  fof(f18,plain,(
% 2.44/0.99    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f17])).
% 2.44/0.99  
% 2.44/0.99  fof(f28,plain,(
% 2.44/0.99    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 2.44/0.99    introduced(choice_axiom,[])).
% 2.44/0.99  
% 2.44/0.99  fof(f29,plain,(
% 2.44/0.99    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f28])).
% 2.44/0.99  
% 2.44/0.99  fof(f47,plain,(
% 2.44/0.99    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f29])).
% 2.44/0.99  
% 2.44/0.99  fof(f1,axiom,(
% 2.44/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f11,plain,(
% 2.44/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.44/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.44/0.99  
% 2.44/0.99  fof(f12,plain,(
% 2.44/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.44/0.99    inference(ennf_transformation,[],[f11])).
% 2.44/0.99  
% 2.44/0.99  fof(f44,plain,(
% 2.44/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.44/0.99    inference(cnf_transformation,[],[f12])).
% 2.44/0.99  
% 2.44/0.99  fof(f54,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f32])).
% 2.44/0.99  
% 2.44/0.99  fof(f84,plain,(
% 2.44/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(equality_resolution,[],[f54])).
% 2.44/0.99  
% 2.44/0.99  fof(f3,axiom,(
% 2.44/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.44/0.99  
% 2.44/0.99  fof(f15,plain,(
% 2.44/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.99    inference(ennf_transformation,[],[f3])).
% 2.44/0.99  
% 2.44/0.99  fof(f16,plain,(
% 2.44/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.99    inference(flattening,[],[f15])).
% 2.44/0.99  
% 2.44/0.99  fof(f46,plain,(
% 2.44/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.99    inference(cnf_transformation,[],[f16])).
% 2.44/0.99  
% 2.44/0.99  fof(f69,plain,(
% 2.44/0.99    m1_subset_1(sK6,u1_struct_0(sK1))),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  fof(f70,plain,(
% 2.44/0.99    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.44/0.99    inference(cnf_transformation,[],[f43])).
% 2.44/0.99  
% 2.44/0.99  cnf(c_13,negated_conjecture,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK6) ),
% 2.44/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1017,negated_conjecture,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK6) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1503,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK6) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_14,negated_conjecture,
% 2.44/0.99      ( sK6 = sK8 ),
% 2.44/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1016,negated_conjecture,
% 2.44/0.99      ( sK6 = sK8 ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_15,negated_conjecture,
% 2.44/0.99      ( sK6 = sK7 ),
% 2.44/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1015,negated_conjecture,
% 2.44/0.99      ( sK6 = sK7 ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1526,plain,
% 2.44/0.99      ( sK7 = sK8 ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_1015,c_1016]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1570,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK8) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_1503,c_1016,c_1526]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_19,negated_conjecture,
% 2.44/0.99      ( k1_tsep_1(sK1,sK4,sK5) = sK1 ),
% 2.44/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1011,negated_conjecture,
% 2.44/0.99      ( k1_tsep_1(sK1,sK4,sK5) = sK1 ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_4,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.44/0.99      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.44/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X5,X2)
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.44/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X3)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X5)
% 2.44/0.99      | v2_struct_0(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_25,negated_conjecture,
% 2.44/0.99      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.44/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_753,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.44/0.99      | ~ r1_tmap_1(X5,X1,k2_tmap_1(X2,X1,X3,X5),X4)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X2,X5,X0),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X5,X0)),X4)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X5,X2)
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X5,X0)))
% 2.44/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X3)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X5)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.44/0.99      | sK3 != X3 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_754,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK3,X4),X3)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X2)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(sK3)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_753]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_26,negated_conjecture,
% 2.44/0.99      ( v1_funct_1(sK3) ),
% 2.44/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_758,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X4,X2)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK3,X4),X3)
% 2.44/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_754,c_26]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_759,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,sK3,X4),X3)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X4,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_758]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_994,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
% 2.44/0.99      | ~ r1_tmap_1(X3_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X3_52),X0_53)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X2_52,X0_52,X3_52),X1_52,k2_tmap_1(X2_52,X1_52,sK3,k1_tsep_1(X2_52,X0_52,X3_52)),X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X2_52)
% 2.44/0.99      | ~ m1_pre_topc(X3_52,X2_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_52,X0_52,X3_52)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(X2_52)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(X2_52)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(X2_52)
% 2.44/0.99      | v2_struct_0(X3_52)
% 2.44/0.99      | u1_struct_0(X2_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_759]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1523,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X2_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X2_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X3_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X3_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X2_52,X3_52),X1_52,k2_tmap_1(X0_52,X1_52,sK3,k1_tsep_1(X0_52,X2_52,X3_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X3_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X2_52,X3_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X1_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X1_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X3_52) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2851,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(equality_resolution,[status(thm)],[c_1523]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_29,negated_conjecture,
% 2.44/0.99      ( ~ v2_struct_0(sK2) ),
% 2.44/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_36,plain,
% 2.44/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_28,negated_conjecture,
% 2.44/0.99      ( v2_pre_topc(sK2) ),
% 2.44/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_37,plain,
% 2.44/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_27,negated_conjecture,
% 2.44/0.99      ( l1_pre_topc(sK2) ),
% 2.44/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_38,plain,
% 2.44/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1025,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1833,plain,
% 2.44/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1025]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1835,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),X0_53)
% 2.44/0.99      | ~ r1_tmap_1(X2_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X2_52),X0_53)
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X1_52,X0_52,X2_52),sK2,k2_tmap_1(X1_52,sK2,sK3,k1_tsep_1(X1_52,X0_52,X2_52)),X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X1_52)
% 2.44/0.99      | ~ m1_pre_topc(X2_52,X1_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X2_52))
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X1_52,X0_52,X2_52)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(sK2)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(sK2)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(X2_52)
% 2.44/0.99      | v2_struct_0(sK2)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_994]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1849,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1835]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3375,plain,
% 2.44/0.99      ( v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_2851,c_36,c_37,c_38]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3376,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X2_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X2_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3375]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3396,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(sK1,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.44/0.99      inference(equality_resolution,[status(thm)],[c_3376]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_32,negated_conjecture,
% 2.44/0.99      ( ~ v2_struct_0(sK1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_33,plain,
% 2.44/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_31,negated_conjecture,
% 2.44/0.99      ( v2_pre_topc(sK1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_34,plain,
% 2.44/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_30,negated_conjecture,
% 2.44/0.99      ( l1_pre_topc(sK1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_35,plain,
% 2.44/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_24,negated_conjecture,
% 2.44/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.44/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_41,plain,
% 2.44/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3895,plain,
% 2.44/0.99      ( v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(sK1,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_3396,c_33,c_34,c_35,c_41]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3896,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(sK1,sK2,sK3,X1_52),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) = iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3895]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3911,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK5,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,sK4,sK5))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | v2_struct_0(sK4) = iProver_top
% 2.44/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_1011,c_3896]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3952,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK5,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | v2_struct_0(sK4) = iProver_top
% 2.44/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_3911,c_1011]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_23,negated_conjecture,
% 2.44/0.99      ( ~ v2_struct_0(sK4) ),
% 2.44/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_42,plain,
% 2.44/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_22,negated_conjecture,
% 2.44/0.99      ( m1_pre_topc(sK4,sK1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_43,plain,
% 2.44/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_21,negated_conjecture,
% 2.44/0.99      ( ~ v2_struct_0(sK5) ),
% 2.44/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_44,plain,
% 2.44/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_20,negated_conjecture,
% 2.44/0.99      ( m1_pre_topc(sK5,sK1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_45,plain,
% 2.44/0.99      ( m1_pre_topc(sK5,sK1) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_4032,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_3952,c_42,c_43,c_44,c_45]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_4044,plain,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),sK8) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_1570,c_4032]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_10,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_8,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_161,plain,
% 2.44/0.99      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_10,c_8]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_162,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_161]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_519,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.44/0.99      | sK3 != X2 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_162,c_25]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_520,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(sK3)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_519]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_524,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_520,c_26]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_525,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_524]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1,plain,
% 2.44/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.44/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.44/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_560,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_525,c_1]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_997,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
% 2.44/0.99      | ~ r1_tmap_1(X2_52,X1_52,sK3,X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X2_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(X2_52)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(X2_52)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(X2_52)
% 2.44/0.99      | u1_struct_0(X2_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_560]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1520,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X2_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X2_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,X1_52,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X1_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X1_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2986,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(equality_resolution,[status(thm)],[c_1520]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1834,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),X0_53)
% 2.44/0.99      | ~ r1_tmap_1(X1_52,sK2,sK3,X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X1_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(sK2)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(sK2)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(sK2)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_997]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1853,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1834]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3080,plain,
% 2.44/0.99      ( v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_2986,c_36,c_37,c_38]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3081,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3080]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3096,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.44/0.99      inference(equality_resolution,[status(thm)],[c_3081]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3180,plain,
% 2.44/0.99      ( v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_3096,c_33,c_34,c_35,c_41]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3181,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3180]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_6,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.44/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 2.44/0.99      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X5,X2)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 2.44/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X3)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X5) ),
% 2.44/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_625,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4)
% 2.44/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X5),X1,k2_tmap_1(X2,X1,X3,k1_tsep_1(X2,X0,X5)),X4)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X5,X2)
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 2.44/0.99      | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X2,X0,X5)))
% 2.44/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(X3)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X5)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.44/0.99      | sK3 != X3 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_626,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X4,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(sK3)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_625]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_630,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_pre_topc(X4,X2)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
% 2.44/0.99      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_626,c_26]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_631,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ r1_tmap_1(k1_tsep_1(X2,X0,X4),X1,k2_tmap_1(X2,X1,sK3,k1_tsep_1(X2,X0,X4)),X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_pre_topc(X4,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X2,X0,X4)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_630]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_996,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
% 2.44/0.99      | ~ r1_tmap_1(k1_tsep_1(X2_52,X0_52,X3_52),X1_52,k2_tmap_1(X2_52,X1_52,sK3,k1_tsep_1(X2_52,X0_52,X3_52)),X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X2_52)
% 2.44/0.99      | ~ m1_pre_topc(X3_52,X2_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X2_52,X0_52,X3_52)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(X2_52)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(X2_52)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(X2_52)
% 2.44/0.99      | v2_struct_0(X3_52)
% 2.44/0.99      | u1_struct_0(X2_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_631]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1521,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X2_52,X1_52,k2_tmap_1(X0_52,X1_52,sK3,X2_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X2_52,X3_52),X1_52,k2_tmap_1(X0_52,X1_52,sK3,k1_tsep_1(X0_52,X2_52,X3_52)),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X3_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X3_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X2_52,X3_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X1_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X1_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X3_52) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2752,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(equality_resolution,[status(thm)],[c_1521]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3274,plain,
% 2.44/0.99      ( v2_struct_0(X2_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_2752,c_36,c_37,c_38,c_1833,c_1847]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3275,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(X0_52,X1_52,X2_52),sK2,k2_tmap_1(X0_52,sK2,sK3,k1_tsep_1(X0_52,X1_52,X2_52)),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X2_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X2_52) = iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3274]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3294,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.44/0.99      inference(equality_resolution,[status(thm)],[c_3275]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3542,plain,
% 2.44/0.99      ( v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_3294,c_33,c_34,c_35,c_41]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3543,plain,
% 2.44/0.99      ( r1_tmap_1(X0_52,sK2,k2_tmap_1(sK1,sK2,sK3,X0_52),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(k1_tsep_1(sK1,X0_52,X1_52),sK2,k2_tmap_1(sK1,sK2,sK3,k1_tsep_1(sK1,X0_52,X1_52)),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(X0_52,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,X0_52,X1_52))) != iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3542]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3558,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK5,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(k1_tsep_1(sK1,sK4,sK5))) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | v2_struct_0(sK4) = iProver_top
% 2.44/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_1011,c_3543]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3569,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK5,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | v2_struct_0(sK4) = iProver_top
% 2.44/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_3558,c_1011]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3709,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_3569,c_42,c_43,c_44,c_45]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3720,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_3181,c_3709]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_7,plain,
% 2.44/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_61,plain,
% 2.44/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 2.44/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_63,plain,
% 2.44/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_61]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3829,plain,
% 2.44/0.99      ( m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_3720,c_33,c_35,c_63]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3830,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_3829]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_4046,plain,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),X0_53) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,X0_53) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),X0_53) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(X0_53,u1_struct_0(sK5)) != iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_3830,c_4032]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_4065,plain,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),sK8) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top ),
% 2.44/0.99      inference(forward_subsumption_resolution,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_4044,c_4046]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_12,negated_conjecture,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,sK3,sK6)
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
% 2.44/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1018,negated_conjecture,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,sK3,sK6)
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1502,plain,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,sK3,sK6) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1565,plain,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_1502,c_1016]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_16,negated_conjecture,
% 2.44/0.99      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.44/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_48,plain,
% 2.44/0.99      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1031,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) = u1_struct_0(X1_52) | X0_52 != X1_52 ),
% 2.44/0.99      theory(equality) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1042,plain,
% 2.44/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1023,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1052,plain,
% 2.44/0.99      ( sK1 = sK1 ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1023]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2358,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0_52,sK2,sK3,sK8)
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(X0_52,sK2,sK3,sK5),sK8)
% 2.44/0.99      | ~ m1_pre_topc(sK5,X0_52)
% 2.44/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2))))
% 2.44/0.99      | ~ v2_pre_topc(X0_52)
% 2.44/0.99      | ~ v2_pre_topc(sK2)
% 2.44/0.99      | ~ l1_pre_topc(X0_52)
% 2.44/0.99      | ~ l1_pre_topc(sK2)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(sK2)
% 2.44/0.99      | v2_struct_0(sK5)
% 2.44/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1834]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2359,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,sK3,sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(X0_52,sK2,sK3,sK5),sK8) = iProver_top
% 2.44/0.99      | m1_pre_topc(sK5,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top
% 2.44/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_2358]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2361,plain,
% 2.44/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top
% 2.44/0.99      | m1_pre_topc(sK5,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top
% 2.44/0.99      | v2_struct_0(sK5) = iProver_top ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_2359]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2417,plain,
% 2.44/0.99      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) = iProver_top ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_1565,c_33,c_34,c_35,c_36,c_37,c_38,c_41,c_44,c_45,
% 2.44/0.99                 c_48,c_1042,c_1052,c_1833,c_2361]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_11,negated_conjecture,
% 2.44/0.99      ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
% 2.44/0.99      | ~ r1_tmap_1(sK1,sK2,sK3,sK6)
% 2.44/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
% 2.44/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1019,negated_conjecture,
% 2.44/0.99      ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7)
% 2.44/0.99      | ~ r1_tmap_1(sK1,sK2,sK3,sK6)
% 2.44/0.99      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1501,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK7) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK6) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1575,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK1,sK2,sK3,sK5),sK8) != iProver_top ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_1501,c_1016,c_1526]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2422,plain,
% 2.44/0.99      ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK1,sK2,sK3,sK4),sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_2417,c_1575]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3191,plain,
% 2.44/0.99      ( r1_tmap_1(sK1,sK2,sK3,sK8) != iProver_top
% 2.44/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.44/0.99      | v2_struct_0(sK4) = iProver_top ),
% 2.44/0.99      inference(superposition,[status(thm)],[c_3181,c_2422]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_3,plain,
% 2.44/0.99      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 2.44/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X0) ),
% 2.44/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_0,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_9,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_317,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | X5 != X6
% 2.44/0.99      | u1_struct_0(X4) != X7 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_318,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_358,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_connsp_2(X5,X0,X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_318,c_1]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_399,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X5,u1_struct_0(X6))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X6)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X6)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X6)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | X0 != X6
% 2.44/0.99      | X3 != X5
% 2.44/0.99      | sK0(X6,X5) != X7 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_358]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_400,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | v2_struct_0(X0) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_399]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2,plain,
% 2.44/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.44/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.44/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X1) ),
% 2.44/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_378,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/0.99      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 2.44/0.99      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X3)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X3)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X3)
% 2.44/0.99      | X3 != X1
% 2.44/0.99      | X2 != X0
% 2.44/0.99      | sK0(X3,X2) != X4 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_379,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.44/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X1) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_421,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(forward_subsumption_resolution,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_400,c_379]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_438,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4) ),
% 2.44/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_421,c_1]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_462,plain,
% 2.44/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.44/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.44/0.99      | ~ m1_pre_topc(X4,X0)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.44/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(sK0(X0,X3),k1_zfmisc_1(u1_struct_0(X4)))
% 2.44/0.99      | ~ v1_funct_1(X2)
% 2.44/0.99      | ~ v2_pre_topc(X0)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X0)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X4)
% 2.44/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2)
% 2.44/0.99      | sK3 != X2 ),
% 2.44/0.99      inference(resolution_lifted,[status(thm)],[c_438,c_25]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_463,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(sK0(X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v1_funct_1(sK3)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(unflattening,[status(thm)],[c_462]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_467,plain,
% 2.44/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ m1_subset_1(sK0(X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(global_propositional_subsumption,
% 2.44/0.99                [status(thm)],
% 2.44/0.99                [c_463,c_26]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_468,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.44/0.99      | r1_tmap_1(X2,X1,sK3,X3)
% 2.44/0.99      | ~ m1_pre_topc(X0,X2)
% 2.44/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.44/0.99      | ~ m1_subset_1(sK0(X2,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.44/0.99      | ~ v2_pre_topc(X1)
% 2.44/0.99      | ~ v2_pre_topc(X2)
% 2.44/0.99      | ~ l1_pre_topc(X1)
% 2.44/0.99      | ~ l1_pre_topc(X2)
% 2.44/0.99      | v2_struct_0(X0)
% 2.44/0.99      | v2_struct_0(X1)
% 2.44/0.99      | v2_struct_0(X2)
% 2.44/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(renaming,[status(thm)],[c_467]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_998,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK3,X0_52),X0_53)
% 2.44/0.99      | r1_tmap_1(X2_52,X1_52,sK3,X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X2_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(sK0(X2_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(X2_52)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(X2_52)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(X2_52)
% 2.44/0.99      | u1_struct_0(X2_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_468]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1838,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),X0_53)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,sK3,X0_53)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X1_52)
% 2.44/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(sK0(X1_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(sK2)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(sK2)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(sK2)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_998]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2255,plain,
% 2.44/0.99      ( ~ r1_tmap_1(X0_52,sK2,k2_tmap_1(X1_52,sK2,sK3,X0_52),sK8)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,sK3,sK8)
% 2.44/0.99      | ~ m1_pre_topc(X0_52,X1_52)
% 2.44/0.99      | ~ m1_subset_1(sK0(X1_52,sK8),k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.44/0.99      | ~ m1_subset_1(sK8,u1_struct_0(X0_52))
% 2.44/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK2))))
% 2.44/0.99      | ~ v2_pre_topc(X1_52)
% 2.44/0.99      | ~ v2_pre_topc(sK2)
% 2.44/0.99      | ~ l1_pre_topc(X1_52)
% 2.44/0.99      | ~ l1_pre_topc(sK2)
% 2.44/0.99      | v2_struct_0(X0_52)
% 2.44/0.99      | v2_struct_0(X1_52)
% 2.44/0.99      | v2_struct_0(sK2)
% 2.44/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1838]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2256,plain,
% 2.44/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(X1_52,sK2,k2_tmap_1(X0_52,sK2,sK3,X1_52),sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(X0_52,sK2,sK3,sK8) = iProver_top
% 2.44/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 2.44/0.99      | m1_subset_1(sK0(X0_52,sK8),k1_zfmisc_1(u1_struct_0(X1_52))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(X1_52)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top
% 2.44/0.99      | v2_struct_0(X1_52) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_2255]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_2258,plain,
% 2.44/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.44/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.44/0.99      | r1_tmap_1(sK1,sK2,k2_tmap_1(sK1,sK2,sK3,sK1),sK8) != iProver_top
% 2.44/0.99      | r1_tmap_1(sK1,sK2,sK3,sK8) = iProver_top
% 2.44/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.44/0.99      | m1_subset_1(sK0(sK1,sK8),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top
% 2.44/0.99      | v2_struct_0(sK2) = iProver_top ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_2256]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_999,plain,
% 2.44/0.99      ( ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 2.44/0.99      | m1_subset_1(sK0(X0_52,X0_53),k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.44/0.99      | ~ v2_pre_topc(X0_52)
% 2.44/0.99      | ~ l1_pre_topc(X0_52)
% 2.44/0.99      | v2_struct_0(X0_52) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_379]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1986,plain,
% 2.44/0.99      ( m1_subset_1(sK0(X0_52,sK8),k1_zfmisc_1(u1_struct_0(X0_52)))
% 2.44/0.99      | ~ m1_subset_1(sK8,u1_struct_0(X0_52))
% 2.44/0.99      | ~ v2_pre_topc(X0_52)
% 2.44/0.99      | ~ l1_pre_topc(X0_52)
% 2.44/0.99      | v2_struct_0(X0_52) ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_999]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1987,plain,
% 2.44/0.99      ( m1_subset_1(sK0(X0_52,sK8),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(X0_52)) != iProver_top
% 2.44/0.99      | v2_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | l1_pre_topc(X0_52) != iProver_top
% 2.44/0.99      | v2_struct_0(X0_52) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1986]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1989,plain,
% 2.44/0.99      ( m1_subset_1(sK0(sK1,sK8),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.44/0.99      | m1_subset_1(sK8,u1_struct_0(sK1)) != iProver_top
% 2.44/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.44/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.44/0.99      | v2_struct_0(sK1) = iProver_top ),
% 2.44/0.99      inference(instantiation,[status(thm)],[c_1987]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_18,negated_conjecture,
% 2.44/0.99      ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
% 2.44/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1012,negated_conjecture,
% 2.44/0.99      ( m1_subset_1(sK6,u1_struct_0(sK1)) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1506,plain,
% 2.44/0.99      ( m1_subset_1(sK6,u1_struct_0(sK1)) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1554,plain,
% 2.44/0.99      ( m1_subset_1(sK8,u1_struct_0(sK1)) = iProver_top ),
% 2.44/0.99      inference(light_normalisation,[status(thm)],[c_1506,c_1016]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_17,negated_conjecture,
% 2.44/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.44/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1013,negated_conjecture,
% 2.44/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.44/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1505,plain,
% 2.44/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.44/0.99      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 2.44/0.99  
% 2.44/0.99  cnf(c_1551,plain,
% 2.44/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.44/1.00      inference(light_normalisation,[status(thm)],[c_1505,c_1526]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(contradiction,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(minisat,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4065,c_3191,c_2417,c_2258,c_1989,c_1833,c_1554,c_1551,
% 2.44/1.00                 c_1052,c_1042,c_63,c_48,c_43,c_42,c_41,c_38,c_37,c_36,
% 2.44/1.00                 c_35,c_34,c_33]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.01
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.02
% 2.44/1.00  total_time:                             0.16
% 2.44/1.00  num_of_symbols:                         58
% 2.44/1.00  num_of_terms:                           3380
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    9
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        3
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        0
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       152
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        14
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        6
% 2.44/1.00  pred_elim:                              4
% 2.44/1.00  pred_elim_cl:                           5
% 2.44/1.00  pred_elim_cycles:                       6
% 2.44/1.00  merged_defs:                            0
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          0
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.012
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                28
% 2.44/1.00  conjectures:                            20
% 2.44/1.00  epr:                                    13
% 2.44/1.00  horn:                                   19
% 2.44/1.00  ground:                                 20
% 2.44/1.00  unary:                                  17
% 2.44/1.00  binary:                                 3
% 2.44/1.00  lits:                                   121
% 2.44/1.00  lits_eq:                                13
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                0
% 2.44/1.00  fd_pseudo_cond:                         0
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      27
% 2.44/1.00  prop_fast_solver_calls:                 1993
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    1068
% 2.44/1.00  prop_preprocess_simplified:             4407
% 2.44/1.00  prop_fo_subsumed:                       76
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    343
% 2.44/1.00  inst_num_in_passive:                    10
% 2.44/1.00  inst_num_in_active:                     262
% 2.44/1.00  inst_num_in_unprocessed:                71
% 2.44/1.00  inst_num_of_loops:                      270
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          5
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      112
% 2.44/1.00  inst_num_of_non_proper_insts:           371
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       156
% 2.44/1.00  res_forward_subset_subsumed:            62
% 2.44/1.00  res_backward_subset_subsumed:           0
% 2.44/1.00  res_forward_subsumed:                   0
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     4
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       301
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      72
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     56
% 2.44/1.00  sup_num_in_active:                      52
% 2.44/1.00  sup_num_in_passive:                     4
% 2.44/1.00  sup_num_of_loops:                       52
% 2.44/1.00  sup_fw_superposition:                   26
% 2.44/1.00  sup_bw_superposition:                   14
% 2.44/1.00  sup_immediate_simplified:               14
% 2.44/1.00  sup_given_eliminated:                   0
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    0
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 7
% 2.44/1.00  sim_bw_subset_subsumed:                 2
% 2.44/1.00  sim_fw_subsumed:                        3
% 2.44/1.00  sim_bw_subsumed:                        0
% 2.44/1.00  sim_fw_subsumption_res:                 1
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      6
% 2.44/1.00  sim_eq_tautology_del:                   0
% 2.44/1.00  sim_eq_res_simp:                        0
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     0
% 2.44/1.00  sim_light_normalised:                   9
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
