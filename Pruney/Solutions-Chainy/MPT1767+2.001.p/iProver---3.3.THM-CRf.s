%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:58 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1103)

% Comments   : 
%------------------------------------------------------------------------------
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f19])).

fof(f7,conjecture,(
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
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
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
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK5,X3)),k2_tmap_1(X0,X1,sK5,X2))
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,k2_tmap_1(X0,X1,X4,sK4)),k2_tmap_1(X0,X1,X4,X2))
            & m1_pre_topc(X2,sK4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
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
                ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK3))
                & m1_pre_topc(sK3,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,k2_tmap_1(X0,sK2,X4,X3)),k2_tmap_1(X0,sK2,X4,X2))
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,k2_tmap_1(sK1,X1,X4,X3)),k2_tmap_1(sK1,X1,X4,X2))
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1))
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

fof(f31,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))
    & m1_pre_topc(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f30,f29,f28,f27,f26])).

fof(f51,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_9,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_279,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,k2_tmap_1(X2_49,X1_49,X1_50,X0_49))
    | r2_funct_2(u1_struct_0(X3_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k2_tmap_1(X2_49,X1_49,X1_50,X3_49))
    | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ v1_funct_2(X1_50,u1_struct_0(X2_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X3_49,X0_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
    | v2_struct_0(X3_49)
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v1_funct_1(X1_50)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1229,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK2),X0_50,k2_tmap_1(X1_49,sK2,X1_50,X0_49))
    | r2_funct_2(u1_struct_0(X2_49),u1_struct_0(sK2),k3_tmap_1(X1_49,sK2,X0_49,X2_49,X0_50),k2_tmap_1(X1_49,sK2,X1_50,X2_49))
    | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK2))
    | ~ v1_funct_2(X1_50,u1_struct_0(X1_49),u1_struct_0(sK2))
    | ~ m1_pre_topc(X2_49,X0_49)
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X2_49,X1_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_49),u1_struct_0(sK2))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | v2_struct_0(X2_49)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X1_50)
    | ~ v1_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_7108,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_273,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_748,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_276,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_745,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_284,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X3_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50)
    | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X3_49)) = k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_737,plain,
    ( k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k3_tmap_1(X3_49,X1_49,X0_49,X2_49,X0_50)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_pre_topc(X2_49,X0_49) != iProver_top
    | m1_pre_topc(X0_49,X3_49) != iProver_top
    | m1_pre_topc(X2_49,X3_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X3_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X3_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X3_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_2487,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(X0_49,sK1) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_737])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_35,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2644,plain,
    ( v2_pre_topc(X1_49) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(X0_49,sK1) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2487,c_28,c_29,c_30,c_35,c_36,c_37,c_1103])).

cnf(c_2645,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(X0_49,sK1) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_2644])).

cnf(c_2658,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK1,sK2,sK1,sK4,sK5)
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_748,c_2645])).

cnf(c_3,plain,
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
    inference(cnf_transformation,[],[f35])).

cnf(c_285,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X2_49,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X0_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X0_49)
    | ~ v1_funct_1(X0_50)
    | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k2_tmap_1(X0_49,X1_49,X0_50,X2_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_736,plain,
    ( k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k2_tmap_1(X0_49,X1_49,X0_50,X2_49)
    | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_pre_topc(X2_49,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_1677,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k2_tmap_1(sK1,sK2,sK5,X0_49)
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_49,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_736])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2124,plain,
    ( m1_pre_topc(X0_49,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k2_tmap_1(sK1,sK2,sK5,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1677,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36])).

cnf(c_2125,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k2_tmap_1(sK1,sK2,sK5,X0_49)
    | m1_pre_topc(X0_49,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2124])).

cnf(c_2132,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK1,sK2,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_748,c_2125])).

cnf(c_2692,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK4,sK5) = k2_tmap_1(sK1,sK2,sK5,sK4)
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2658,c_2132])).

cnf(c_34,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_43,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_45,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_3276,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK4,sK5) = k2_tmap_1(sK1,sK2,sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_25,c_26,c_27,c_34,c_45])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_283,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_738,plain,
    ( v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_pre_topc(X0_49,X2_49) != iProver_top
    | m1_pre_topc(X3_49,X2_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49)))) = iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X2_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X2_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_0,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_288,plain,
    ( r2_funct_2(X0_51,X1_51,X0_50,X1_50)
    | ~ v1_funct_2(X1_50,X0_51,X1_51)
    | ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X1_50)
    | ~ v1_funct_1(X0_50)
    | k1_funct_1(X1_50,sK0(X0_51,X0_50,X1_50)) != k1_funct_1(X0_50,sK0(X0_51,X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_733,plain,
    ( k1_funct_1(X0_50,sK0(X0_51,X1_50,X0_50)) != k1_funct_1(X1_50,sK0(X0_51,X1_50,X0_50))
    | r2_funct_2(X0_51,X1_51,X1_50,X0_50) = iProver_top
    | v1_funct_2(X1_50,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_1220,plain,
    ( r2_funct_2(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_733])).

cnf(c_1796,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50)) = iProver_top
    | v1_funct_2(X0_50,u1_struct_0(X3_49),u1_struct_0(X1_49)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50),u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_pre_topc(X3_49,X2_49) != iProver_top
    | m1_pre_topc(X0_49,X2_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X2_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X2_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50)) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_1220])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_281,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X2_49)
    | v2_struct_0(X1_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_740,plain,
    ( v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_pre_topc(X0_49,X2_49) != iProver_top
    | m1_pre_topc(X3_49,X2_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X2_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X2_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_282,plain,
    ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),u1_struct_0(X3_49),u1_struct_0(X1_49))
    | ~ m1_pre_topc(X3_49,X2_49)
    | ~ m1_pre_topc(X0_49,X2_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | v2_struct_0(X1_49)
    | v2_struct_0(X2_49)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(X2_49)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(X2_49)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_739,plain,
    ( v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),u1_struct_0(X3_49),u1_struct_0(X1_49)) = iProver_top
    | m1_pre_topc(X0_49,X2_49) != iProver_top
    | m1_pre_topc(X3_49,X2_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X2_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X2_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_2835,plain,
    ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50)) = iProver_top
    | v1_funct_2(X0_50,u1_struct_0(X3_49),u1_struct_0(X1_49)) != iProver_top
    | m1_pre_topc(X0_49,X2_49) != iProver_top
    | m1_pre_topc(X3_49,X2_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(X2_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(X2_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X2_49) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1796,c_740,c_739])).

cnf(c_3282,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_2835])).

cnf(c_3371,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3282])).

cnf(c_1694,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_740])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1068,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(sK1,X1_49)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(X1_49)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1_49)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1_49)
    | ~ l1_pre_topc(sK2)
    | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1069,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_2317,plain,
    ( v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1694,c_28,c_29,c_30,c_35,c_36])).

cnf(c_2318,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(sK1,X1_49) != iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v2_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2317])).

cnf(c_3281,plain,
    ( m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_2318])).

cnf(c_3370,plain,
    ( ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3281])).

cnf(c_3280,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_739])).

cnf(c_3369,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3280])).

cnf(c_3279,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK4,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_738])).

cnf(c_3368,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3279])).

cnf(c_44,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7108,c_3371,c_3370,c_3369,c_3368,c_44,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:15:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.64/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.99  
% 3.64/0.99  ------  iProver source info
% 3.64/0.99  
% 3.64/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.99  git: non_committed_changes: false
% 3.64/0.99  git: last_make_outside_of_git: false
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    --mode clausify
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             all
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         305.
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/0.99  --trig_cnt_out                          false
% 3.64/0.99  --trig_cnt_out_tolerance                1.
% 3.64/0.99  --trig_cnt_out_sk_spl                   false
% 3.64/0.99  --abstr_cl_out                          false
% 3.64/0.99  
% 3.64/0.99  ------ Global Options
% 3.64/0.99  
% 3.64/0.99  --schedule                              default
% 3.64/0.99  --add_important_lit                     false
% 3.64/0.99  --prop_solver_per_cl                    1000
% 3.64/0.99  --min_unsat_core                        false
% 3.64/0.99  --soft_assumptions                      false
% 3.64/0.99  --soft_lemma_size                       3
% 3.64/0.99  --prop_impl_unit_size                   0
% 3.64/0.99  --prop_impl_unit                        []
% 3.64/0.99  --share_sel_clauses                     true
% 3.64/0.99  --reset_solvers                         false
% 3.64/0.99  --bc_imp_inh                            [conj_cone]
% 3.64/0.99  --conj_cone_tolerance                   3.
% 3.64/0.99  --extra_neg_conj                        none
% 3.64/0.99  --large_theory_mode                     true
% 3.64/0.99  --prolific_symb_bound                   200
% 3.64/0.99  --lt_threshold                          2000
% 3.64/0.99  --clause_weak_htbl                      true
% 3.64/0.99  --gc_record_bc_elim                     false
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing Options
% 3.64/0.99  
% 3.64/0.99  --preprocessing_flag                    true
% 3.64/0.99  --time_out_prep_mult                    0.1
% 3.64/0.99  --splitting_mode                        input
% 3.64/0.99  --splitting_grd                         true
% 3.64/0.99  --splitting_cvd                         false
% 3.64/0.99  --splitting_cvd_svl                     false
% 3.64/0.99  --splitting_nvd                         32
% 3.64/0.99  --sub_typing                            true
% 3.64/0.99  --prep_gs_sim                           true
% 3.64/0.99  --prep_unflatten                        true
% 3.64/0.99  --prep_res_sim                          true
% 3.64/0.99  --prep_upred                            true
% 3.64/0.99  --prep_sem_filter                       exhaustive
% 3.64/0.99  --prep_sem_filter_out                   false
% 3.64/0.99  --pred_elim                             true
% 3.64/0.99  --res_sim_input                         true
% 3.64/0.99  --eq_ax_congr_red                       true
% 3.64/0.99  --pure_diseq_elim                       true
% 3.64/0.99  --brand_transform                       false
% 3.64/0.99  --non_eq_to_eq                          false
% 3.64/0.99  --prep_def_merge                        true
% 3.64/0.99  --prep_def_merge_prop_impl              false
% 3.64/0.99  --prep_def_merge_mbd                    true
% 3.64/0.99  --prep_def_merge_tr_red                 false
% 3.64/0.99  --prep_def_merge_tr_cl                  false
% 3.64/0.99  --smt_preprocessing                     true
% 3.64/0.99  --smt_ac_axioms                         fast
% 3.64/0.99  --preprocessed_out                      false
% 3.64/0.99  --preprocessed_stats                    false
% 3.64/0.99  
% 3.64/0.99  ------ Abstraction refinement Options
% 3.64/0.99  
% 3.64/0.99  --abstr_ref                             []
% 3.64/0.99  --abstr_ref_prep                        false
% 3.64/0.99  --abstr_ref_until_sat                   false
% 3.64/0.99  --abstr_ref_sig_restrict                funpre
% 3.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.99  --abstr_ref_under                       []
% 3.64/0.99  
% 3.64/0.99  ------ SAT Options
% 3.64/0.99  
% 3.64/0.99  --sat_mode                              false
% 3.64/0.99  --sat_fm_restart_options                ""
% 3.64/0.99  --sat_gr_def                            false
% 3.64/0.99  --sat_epr_types                         true
% 3.64/0.99  --sat_non_cyclic_types                  false
% 3.64/0.99  --sat_finite_models                     false
% 3.64/0.99  --sat_fm_lemmas                         false
% 3.64/0.99  --sat_fm_prep                           false
% 3.64/0.99  --sat_fm_uc_incr                        true
% 3.64/0.99  --sat_out_model                         small
% 3.64/0.99  --sat_out_clauses                       false
% 3.64/0.99  
% 3.64/0.99  ------ QBF Options
% 3.64/0.99  
% 3.64/0.99  --qbf_mode                              false
% 3.64/0.99  --qbf_elim_univ                         false
% 3.64/0.99  --qbf_dom_inst                          none
% 3.64/0.99  --qbf_dom_pre_inst                      false
% 3.64/0.99  --qbf_sk_in                             false
% 3.64/0.99  --qbf_pred_elim                         true
% 3.64/0.99  --qbf_split                             512
% 3.64/0.99  
% 3.64/0.99  ------ BMC1 Options
% 3.64/0.99  
% 3.64/0.99  --bmc1_incremental                      false
% 3.64/0.99  --bmc1_axioms                           reachable_all
% 3.64/0.99  --bmc1_min_bound                        0
% 3.64/0.99  --bmc1_max_bound                        -1
% 3.64/0.99  --bmc1_max_bound_default                -1
% 3.64/0.99  --bmc1_symbol_reachability              true
% 3.64/0.99  --bmc1_property_lemmas                  false
% 3.64/0.99  --bmc1_k_induction                      false
% 3.64/0.99  --bmc1_non_equiv_states                 false
% 3.64/0.99  --bmc1_deadlock                         false
% 3.64/0.99  --bmc1_ucm                              false
% 3.64/0.99  --bmc1_add_unsat_core                   none
% 3.64/0.99  --bmc1_unsat_core_children              false
% 3.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.99  --bmc1_out_stat                         full
% 3.64/0.99  --bmc1_ground_init                      false
% 3.64/0.99  --bmc1_pre_inst_next_state              false
% 3.64/0.99  --bmc1_pre_inst_state                   false
% 3.64/0.99  --bmc1_pre_inst_reach_state             false
% 3.64/0.99  --bmc1_out_unsat_core                   false
% 3.64/0.99  --bmc1_aig_witness_out                  false
% 3.64/0.99  --bmc1_verbose                          false
% 3.64/0.99  --bmc1_dump_clauses_tptp                false
% 3.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.99  --bmc1_dump_file                        -
% 3.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.99  --bmc1_ucm_extend_mode                  1
% 3.64/0.99  --bmc1_ucm_init_mode                    2
% 3.64/0.99  --bmc1_ucm_cone_mode                    none
% 3.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.99  --bmc1_ucm_relax_model                  4
% 3.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.99  --bmc1_ucm_layered_model                none
% 3.64/0.99  --bmc1_ucm_max_lemma_size               10
% 3.64/0.99  
% 3.64/0.99  ------ AIG Options
% 3.64/0.99  
% 3.64/0.99  --aig_mode                              false
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation Options
% 3.64/0.99  
% 3.64/0.99  --instantiation_flag                    true
% 3.64/0.99  --inst_sos_flag                         false
% 3.64/0.99  --inst_sos_phase                        true
% 3.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel_side                     num_symb
% 3.64/0.99  --inst_solver_per_active                1400
% 3.64/0.99  --inst_solver_calls_frac                1.
% 3.64/0.99  --inst_passive_queue_type               priority_queues
% 3.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.99  --inst_passive_queues_freq              [25;2]
% 3.64/0.99  --inst_dismatching                      true
% 3.64/0.99  --inst_eager_unprocessed_to_passive     true
% 3.64/0.99  --inst_prop_sim_given                   true
% 3.64/0.99  --inst_prop_sim_new                     false
% 3.64/0.99  --inst_subs_new                         false
% 3.64/0.99  --inst_eq_res_simp                      false
% 3.64/0.99  --inst_subs_given                       false
% 3.64/0.99  --inst_orphan_elimination               true
% 3.64/0.99  --inst_learning_loop_flag               true
% 3.64/0.99  --inst_learning_start                   3000
% 3.64/0.99  --inst_learning_factor                  2
% 3.64/0.99  --inst_start_prop_sim_after_learn       3
% 3.64/0.99  --inst_sel_renew                        solver
% 3.64/0.99  --inst_lit_activity_flag                true
% 3.64/0.99  --inst_restr_to_given                   false
% 3.64/0.99  --inst_activity_threshold               500
% 3.64/0.99  --inst_out_proof                        true
% 3.64/0.99  
% 3.64/0.99  ------ Resolution Options
% 3.64/0.99  
% 3.64/0.99  --resolution_flag                       true
% 3.64/0.99  --res_lit_sel                           adaptive
% 3.64/0.99  --res_lit_sel_side                      none
% 3.64/0.99  --res_ordering                          kbo
% 3.64/0.99  --res_to_prop_solver                    active
% 3.64/0.99  --res_prop_simpl_new                    false
% 3.64/0.99  --res_prop_simpl_given                  true
% 3.64/0.99  --res_passive_queue_type                priority_queues
% 3.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.99  --res_passive_queues_freq               [15;5]
% 3.64/0.99  --res_forward_subs                      full
% 3.64/0.99  --res_backward_subs                     full
% 3.64/0.99  --res_forward_subs_resolution           true
% 3.64/0.99  --res_backward_subs_resolution          true
% 3.64/0.99  --res_orphan_elimination                true
% 3.64/0.99  --res_time_limit                        2.
% 3.64/0.99  --res_out_proof                         true
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Options
% 3.64/0.99  
% 3.64/0.99  --superposition_flag                    true
% 3.64/0.99  --sup_passive_queue_type                priority_queues
% 3.64/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.99  --demod_completeness_check              fast
% 3.64/0.99  --demod_use_ground                      true
% 3.64/0.99  --sup_to_prop_solver                    passive
% 3.64/0.99  --sup_prop_simpl_new                    true
% 3.64/0.99  --sup_prop_simpl_given                  true
% 3.64/0.99  --sup_fun_splitting                     false
% 3.64/0.99  --sup_smt_interval                      50000
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Simplification Setup
% 3.64/0.99  
% 3.64/0.99  --sup_indices_passive                   []
% 3.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_full_bw                           [BwDemod]
% 3.64/0.99  --sup_immed_triv                        [TrivRules]
% 3.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_immed_bw_main                     []
% 3.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  
% 3.64/0.99  ------ Combination Options
% 3.64/0.99  
% 3.64/0.99  --comb_res_mult                         3
% 3.64/0.99  --comb_sup_mult                         2
% 3.64/0.99  --comb_inst_mult                        10
% 3.64/0.99  
% 3.64/0.99  ------ Debug Options
% 3.64/0.99  
% 3.64/0.99  --dbg_backtrace                         false
% 3.64/0.99  --dbg_dump_prop_clauses                 false
% 3.64/0.99  --dbg_dump_prop_clauses_file            -
% 3.64/0.99  --dbg_out_stat                          false
% 3.64/0.99  ------ Parsing...
% 3.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.99  ------ Proving...
% 3.64/0.99  ------ Problem Properties 
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  clauses                                 25
% 3.64/0.99  conjectures                             15
% 3.64/0.99  EPR                                     13
% 3.64/0.99  Horn                                    18
% 3.64/0.99  unary                                   15
% 3.64/0.99  binary                                  1
% 3.64/0.99  lits                                    121
% 3.64/0.99  lits eq                                 4
% 3.64/0.99  fd_pure                                 0
% 3.64/0.99  fd_pseudo                               0
% 3.64/0.99  fd_cond                                 0
% 3.64/0.99  fd_pseudo_cond                          0
% 3.64/0.99  AC symbols                              0
% 3.64/0.99  
% 3.64/0.99  ------ Schedule dynamic 5 is on 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ 
% 3.64/0.99  Current options:
% 3.64/0.99  ------ 
% 3.64/0.99  
% 3.64/0.99  ------ Input Options
% 3.64/0.99  
% 3.64/0.99  --out_options                           all
% 3.64/0.99  --tptp_safe_out                         true
% 3.64/0.99  --problem_path                          ""
% 3.64/0.99  --include_path                          ""
% 3.64/0.99  --clausifier                            res/vclausify_rel
% 3.64/0.99  --clausifier_options                    --mode clausify
% 3.64/0.99  --stdin                                 false
% 3.64/0.99  --stats_out                             all
% 3.64/0.99  
% 3.64/0.99  ------ General Options
% 3.64/0.99  
% 3.64/0.99  --fof                                   false
% 3.64/0.99  --time_out_real                         305.
% 3.64/0.99  --time_out_virtual                      -1.
% 3.64/0.99  --symbol_type_check                     false
% 3.64/0.99  --clausify_out                          false
% 3.64/0.99  --sig_cnt_out                           false
% 3.64/0.99  --trig_cnt_out                          false
% 3.64/0.99  --trig_cnt_out_tolerance                1.
% 3.64/0.99  --trig_cnt_out_sk_spl                   false
% 3.64/0.99  --abstr_cl_out                          false
% 3.64/0.99  
% 3.64/0.99  ------ Global Options
% 3.64/0.99  
% 3.64/0.99  --schedule                              default
% 3.64/0.99  --add_important_lit                     false
% 3.64/0.99  --prop_solver_per_cl                    1000
% 3.64/0.99  --min_unsat_core                        false
% 3.64/0.99  --soft_assumptions                      false
% 3.64/0.99  --soft_lemma_size                       3
% 3.64/0.99  --prop_impl_unit_size                   0
% 3.64/0.99  --prop_impl_unit                        []
% 3.64/0.99  --share_sel_clauses                     true
% 3.64/0.99  --reset_solvers                         false
% 3.64/0.99  --bc_imp_inh                            [conj_cone]
% 3.64/0.99  --conj_cone_tolerance                   3.
% 3.64/0.99  --extra_neg_conj                        none
% 3.64/0.99  --large_theory_mode                     true
% 3.64/0.99  --prolific_symb_bound                   200
% 3.64/0.99  --lt_threshold                          2000
% 3.64/0.99  --clause_weak_htbl                      true
% 3.64/0.99  --gc_record_bc_elim                     false
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing Options
% 3.64/0.99  
% 3.64/0.99  --preprocessing_flag                    true
% 3.64/0.99  --time_out_prep_mult                    0.1
% 3.64/0.99  --splitting_mode                        input
% 3.64/0.99  --splitting_grd                         true
% 3.64/0.99  --splitting_cvd                         false
% 3.64/0.99  --splitting_cvd_svl                     false
% 3.64/0.99  --splitting_nvd                         32
% 3.64/0.99  --sub_typing                            true
% 3.64/0.99  --prep_gs_sim                           true
% 3.64/0.99  --prep_unflatten                        true
% 3.64/0.99  --prep_res_sim                          true
% 3.64/0.99  --prep_upred                            true
% 3.64/0.99  --prep_sem_filter                       exhaustive
% 3.64/0.99  --prep_sem_filter_out                   false
% 3.64/0.99  --pred_elim                             true
% 3.64/0.99  --res_sim_input                         true
% 3.64/0.99  --eq_ax_congr_red                       true
% 3.64/0.99  --pure_diseq_elim                       true
% 3.64/0.99  --brand_transform                       false
% 3.64/0.99  --non_eq_to_eq                          false
% 3.64/0.99  --prep_def_merge                        true
% 3.64/0.99  --prep_def_merge_prop_impl              false
% 3.64/0.99  --prep_def_merge_mbd                    true
% 3.64/0.99  --prep_def_merge_tr_red                 false
% 3.64/0.99  --prep_def_merge_tr_cl                  false
% 3.64/0.99  --smt_preprocessing                     true
% 3.64/0.99  --smt_ac_axioms                         fast
% 3.64/0.99  --preprocessed_out                      false
% 3.64/0.99  --preprocessed_stats                    false
% 3.64/0.99  
% 3.64/0.99  ------ Abstraction refinement Options
% 3.64/0.99  
% 3.64/0.99  --abstr_ref                             []
% 3.64/0.99  --abstr_ref_prep                        false
% 3.64/0.99  --abstr_ref_until_sat                   false
% 3.64/0.99  --abstr_ref_sig_restrict                funpre
% 3.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.99  --abstr_ref_under                       []
% 3.64/0.99  
% 3.64/0.99  ------ SAT Options
% 3.64/0.99  
% 3.64/0.99  --sat_mode                              false
% 3.64/0.99  --sat_fm_restart_options                ""
% 3.64/0.99  --sat_gr_def                            false
% 3.64/0.99  --sat_epr_types                         true
% 3.64/0.99  --sat_non_cyclic_types                  false
% 3.64/0.99  --sat_finite_models                     false
% 3.64/0.99  --sat_fm_lemmas                         false
% 3.64/0.99  --sat_fm_prep                           false
% 3.64/0.99  --sat_fm_uc_incr                        true
% 3.64/0.99  --sat_out_model                         small
% 3.64/0.99  --sat_out_clauses                       false
% 3.64/0.99  
% 3.64/0.99  ------ QBF Options
% 3.64/0.99  
% 3.64/0.99  --qbf_mode                              false
% 3.64/0.99  --qbf_elim_univ                         false
% 3.64/0.99  --qbf_dom_inst                          none
% 3.64/0.99  --qbf_dom_pre_inst                      false
% 3.64/0.99  --qbf_sk_in                             false
% 3.64/0.99  --qbf_pred_elim                         true
% 3.64/0.99  --qbf_split                             512
% 3.64/0.99  
% 3.64/0.99  ------ BMC1 Options
% 3.64/0.99  
% 3.64/0.99  --bmc1_incremental                      false
% 3.64/0.99  --bmc1_axioms                           reachable_all
% 3.64/0.99  --bmc1_min_bound                        0
% 3.64/0.99  --bmc1_max_bound                        -1
% 3.64/0.99  --bmc1_max_bound_default                -1
% 3.64/0.99  --bmc1_symbol_reachability              true
% 3.64/0.99  --bmc1_property_lemmas                  false
% 3.64/0.99  --bmc1_k_induction                      false
% 3.64/0.99  --bmc1_non_equiv_states                 false
% 3.64/0.99  --bmc1_deadlock                         false
% 3.64/0.99  --bmc1_ucm                              false
% 3.64/0.99  --bmc1_add_unsat_core                   none
% 3.64/0.99  --bmc1_unsat_core_children              false
% 3.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.99  --bmc1_out_stat                         full
% 3.64/0.99  --bmc1_ground_init                      false
% 3.64/0.99  --bmc1_pre_inst_next_state              false
% 3.64/0.99  --bmc1_pre_inst_state                   false
% 3.64/0.99  --bmc1_pre_inst_reach_state             false
% 3.64/0.99  --bmc1_out_unsat_core                   false
% 3.64/0.99  --bmc1_aig_witness_out                  false
% 3.64/0.99  --bmc1_verbose                          false
% 3.64/0.99  --bmc1_dump_clauses_tptp                false
% 3.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.99  --bmc1_dump_file                        -
% 3.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.99  --bmc1_ucm_extend_mode                  1
% 3.64/0.99  --bmc1_ucm_init_mode                    2
% 3.64/0.99  --bmc1_ucm_cone_mode                    none
% 3.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.99  --bmc1_ucm_relax_model                  4
% 3.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.99  --bmc1_ucm_layered_model                none
% 3.64/0.99  --bmc1_ucm_max_lemma_size               10
% 3.64/0.99  
% 3.64/0.99  ------ AIG Options
% 3.64/0.99  
% 3.64/0.99  --aig_mode                              false
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation Options
% 3.64/0.99  
% 3.64/0.99  --instantiation_flag                    true
% 3.64/0.99  --inst_sos_flag                         false
% 3.64/0.99  --inst_sos_phase                        true
% 3.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.99  --inst_lit_sel_side                     none
% 3.64/0.99  --inst_solver_per_active                1400
% 3.64/0.99  --inst_solver_calls_frac                1.
% 3.64/0.99  --inst_passive_queue_type               priority_queues
% 3.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.99  --inst_passive_queues_freq              [25;2]
% 3.64/0.99  --inst_dismatching                      true
% 3.64/0.99  --inst_eager_unprocessed_to_passive     true
% 3.64/0.99  --inst_prop_sim_given                   true
% 3.64/0.99  --inst_prop_sim_new                     false
% 3.64/0.99  --inst_subs_new                         false
% 3.64/0.99  --inst_eq_res_simp                      false
% 3.64/0.99  --inst_subs_given                       false
% 3.64/0.99  --inst_orphan_elimination               true
% 3.64/0.99  --inst_learning_loop_flag               true
% 3.64/0.99  --inst_learning_start                   3000
% 3.64/0.99  --inst_learning_factor                  2
% 3.64/0.99  --inst_start_prop_sim_after_learn       3
% 3.64/0.99  --inst_sel_renew                        solver
% 3.64/0.99  --inst_lit_activity_flag                true
% 3.64/0.99  --inst_restr_to_given                   false
% 3.64/0.99  --inst_activity_threshold               500
% 3.64/0.99  --inst_out_proof                        true
% 3.64/0.99  
% 3.64/0.99  ------ Resolution Options
% 3.64/0.99  
% 3.64/0.99  --resolution_flag                       false
% 3.64/0.99  --res_lit_sel                           adaptive
% 3.64/0.99  --res_lit_sel_side                      none
% 3.64/0.99  --res_ordering                          kbo
% 3.64/0.99  --res_to_prop_solver                    active
% 3.64/0.99  --res_prop_simpl_new                    false
% 3.64/0.99  --res_prop_simpl_given                  true
% 3.64/0.99  --res_passive_queue_type                priority_queues
% 3.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.99  --res_passive_queues_freq               [15;5]
% 3.64/0.99  --res_forward_subs                      full
% 3.64/0.99  --res_backward_subs                     full
% 3.64/0.99  --res_forward_subs_resolution           true
% 3.64/0.99  --res_backward_subs_resolution          true
% 3.64/0.99  --res_orphan_elimination                true
% 3.64/0.99  --res_time_limit                        2.
% 3.64/0.99  --res_out_proof                         true
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Options
% 3.64/0.99  
% 3.64/0.99  --superposition_flag                    true
% 3.64/0.99  --sup_passive_queue_type                priority_queues
% 3.64/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.64/0.99  --demod_completeness_check              fast
% 3.64/0.99  --demod_use_ground                      true
% 3.64/0.99  --sup_to_prop_solver                    passive
% 3.64/0.99  --sup_prop_simpl_new                    true
% 3.64/0.99  --sup_prop_simpl_given                  true
% 3.64/0.99  --sup_fun_splitting                     false
% 3.64/0.99  --sup_smt_interval                      50000
% 3.64/0.99  
% 3.64/0.99  ------ Superposition Simplification Setup
% 3.64/0.99  
% 3.64/0.99  --sup_indices_passive                   []
% 3.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_full_bw                           [BwDemod]
% 3.64/0.99  --sup_immed_triv                        [TrivRules]
% 3.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_immed_bw_main                     []
% 3.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.99  
% 3.64/0.99  ------ Combination Options
% 3.64/0.99  
% 3.64/0.99  --comb_res_mult                         3
% 3.64/0.99  --comb_sup_mult                         2
% 3.64/0.99  --comb_inst_mult                        10
% 3.64/0.99  
% 3.64/0.99  ------ Debug Options
% 3.64/0.99  
% 3.64/0.99  --dbg_backtrace                         false
% 3.64/0.99  --dbg_dump_prop_clauses                 false
% 3.64/0.99  --dbg_dump_prop_clauses_file            -
% 3.64/0.99  --dbg_out_stat                          false
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  ------ Proving...
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS status Theorem for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  fof(f6,axiom,(
% 3.64/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f18,plain,(
% 3.64/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f6])).
% 3.64/0.99  
% 3.64/0.99  fof(f19,plain,(
% 3.64/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.64/0.99    inference(flattening,[],[f18])).
% 3.64/0.99  
% 3.64/0.99  fof(f41,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f19])).
% 3.64/0.99  
% 3.64/0.99  fof(f7,conjecture,(
% 3.64/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f8,negated_conjecture,(
% 3.64/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.64/0.99    inference(negated_conjecture,[],[f7])).
% 3.64/0.99  
% 3.64/0.99  fof(f20,plain,(
% 3.64/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f8])).
% 3.64/0.99  
% 3.64/0.99  fof(f21,plain,(
% 3.64/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.64/0.99    inference(flattening,[],[f20])).
% 3.64/0.99  
% 3.64/0.99  fof(f30,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,sK5,X3)),k2_tmap_1(X0,X1,sK5,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f29,plain,(
% 3.64/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,k2_tmap_1(X0,X1,X4,sK4)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,sK4) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f28,plain,(
% 3.64/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,sK3)) & m1_pre_topc(sK3,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f27,plain,(
% 3.64/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,k2_tmap_1(X0,sK2,X4,X3)),k2_tmap_1(X0,sK2,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f26,plain,(
% 3.64/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,k2_tmap_1(sK1,X1,X4,X3)),k2_tmap_1(sK1,X1,X4,X2)) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f31,plain,(
% 3.64/0.99    ((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) & m1_pre_topc(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f21,f30,f29,f28,f27,f26])).
% 3.64/0.99  
% 3.64/0.99  fof(f51,plain,(
% 3.64/0.99    m1_pre_topc(sK4,sK1)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f54,plain,(
% 3.64/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f3,axiom,(
% 3.64/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f13,plain,(
% 3.64/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f3])).
% 3.64/0.99  
% 3.64/0.99  fof(f14,plain,(
% 3.64/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.64/0.99    inference(flattening,[],[f13])).
% 3.64/0.99  
% 3.64/0.99  fof(f36,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f14])).
% 3.64/0.99  
% 3.64/0.99  fof(f45,plain,(
% 3.64/0.99    ~v2_struct_0(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f46,plain,(
% 3.64/0.99    v2_pre_topc(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f47,plain,(
% 3.64/0.99    l1_pre_topc(sK2)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f52,plain,(
% 3.64/0.99    v1_funct_1(sK5)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f53,plain,(
% 3.64/0.99    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f2,axiom,(
% 3.64/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f11,plain,(
% 3.64/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f2])).
% 3.64/0.99  
% 3.64/0.99  fof(f12,plain,(
% 3.64/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.64/0.99    inference(flattening,[],[f11])).
% 3.64/0.99  
% 3.64/0.99  fof(f35,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f12])).
% 3.64/0.99  
% 3.64/0.99  fof(f42,plain,(
% 3.64/0.99    ~v2_struct_0(sK1)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f43,plain,(
% 3.64/0.99    v2_pre_topc(sK1)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f44,plain,(
% 3.64/0.99    l1_pre_topc(sK1)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f5,axiom,(
% 3.64/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f17,plain,(
% 3.64/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.64/0.99    inference(ennf_transformation,[],[f5])).
% 3.64/0.99  
% 3.64/0.99  fof(f40,plain,(
% 3.64/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f17])).
% 3.64/0.99  
% 3.64/0.99  fof(f4,axiom,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f15,plain,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.64/0.99    inference(ennf_transformation,[],[f4])).
% 3.64/0.99  
% 3.64/0.99  fof(f16,plain,(
% 3.64/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.64/0.99    inference(flattening,[],[f15])).
% 3.64/0.99  
% 3.64/0.99  fof(f39,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f1,axiom,(
% 3.64/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 3.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.99  
% 3.64/0.99  fof(f9,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.64/0.99    inference(ennf_transformation,[],[f1])).
% 3.64/0.99  
% 3.64/0.99  fof(f10,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.64/0.99    inference(flattening,[],[f9])).
% 3.64/0.99  
% 3.64/0.99  fof(f22,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.64/0.99    inference(nnf_transformation,[],[f10])).
% 3.64/0.99  
% 3.64/0.99  fof(f23,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.64/0.99    inference(rectify,[],[f22])).
% 3.64/0.99  
% 3.64/0.99  fof(f24,plain,(
% 3.64/0.99    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 3.64/0.99    introduced(choice_axiom,[])).
% 3.64/0.99  
% 3.64/0.99  fof(f25,plain,(
% 3.64/0.99    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.64/0.99  
% 3.64/0.99  fof(f34,plain,(
% 3.64/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f25])).
% 3.64/0.99  
% 3.64/0.99  fof(f37,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f38,plain,(
% 3.64/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.64/0.99    inference(cnf_transformation,[],[f16])).
% 3.64/0.99  
% 3.64/0.99  fof(f56,plain,(
% 3.64/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f55,plain,(
% 3.64/0.99    m1_pre_topc(sK3,sK4)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f50,plain,(
% 3.64/0.99    ~v2_struct_0(sK4)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f49,plain,(
% 3.64/0.99    m1_pre_topc(sK3,sK1)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  fof(f48,plain,(
% 3.64/0.99    ~v2_struct_0(sK3)),
% 3.64/0.99    inference(cnf_transformation,[],[f31])).
% 3.64/0.99  
% 3.64/0.99  cnf(c_9,plain,
% 3.64/0.99      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 3.64/0.99      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 3.64/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.64/0.99      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 3.64/0.99      | ~ m1_pre_topc(X5,X3)
% 3.64/0.99      | ~ m1_pre_topc(X5,X0)
% 3.64/0.99      | ~ m1_pre_topc(X0,X3)
% 3.64/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.64/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.64/0.99      | v2_struct_0(X3)
% 3.64/0.99      | v2_struct_0(X1)
% 3.64/0.99      | v2_struct_0(X0)
% 3.64/0.99      | v2_struct_0(X5)
% 3.64/0.99      | ~ v2_pre_topc(X1)
% 3.64/0.99      | ~ v2_pre_topc(X3)
% 3.64/0.99      | ~ l1_pre_topc(X1)
% 3.64/0.99      | ~ l1_pre_topc(X3)
% 3.64/0.99      | ~ v1_funct_1(X4)
% 3.64/0.99      | ~ v1_funct_1(X2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_279,plain,
% 3.64/0.99      ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,k2_tmap_1(X2_49,X1_49,X1_50,X0_49))
% 3.64/0.99      | r2_funct_2(u1_struct_0(X3_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k2_tmap_1(X2_49,X1_49,X1_50,X3_49))
% 3.64/0.99      | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ v1_funct_2(X1_50,u1_struct_0(X2_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X2_49)
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X0_49)
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X2_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.64/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_49),u1_struct_0(X1_49))))
% 3.64/0.99      | v2_struct_0(X3_49)
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | v2_struct_0(X0_49)
% 3.64/0.99      | v2_struct_0(X2_49)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X2_49)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(X2_49)
% 3.64/0.99      | ~ v1_funct_1(X1_50)
% 3.64/0.99      | ~ v1_funct_1(X0_50) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1229,plain,
% 3.64/0.99      ( ~ r2_funct_2(u1_struct_0(X0_49),u1_struct_0(sK2),X0_50,k2_tmap_1(X1_49,sK2,X1_50,X0_49))
% 3.64/0.99      | r2_funct_2(u1_struct_0(X2_49),u1_struct_0(sK2),k3_tmap_1(X1_49,sK2,X0_49,X2_49,X0_50),k2_tmap_1(X1_49,sK2,X1_50,X2_49))
% 3.64/0.99      | ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(sK2))
% 3.64/0.99      | ~ v1_funct_2(X1_50,u1_struct_0(X1_49),u1_struct_0(sK2))
% 3.64/0.99      | ~ m1_pre_topc(X2_49,X0_49)
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X1_49)
% 3.64/0.99      | ~ m1_pre_topc(X2_49,X1_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK2))))
% 3.64/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_49),u1_struct_0(sK2))))
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | v2_struct_0(X0_49)
% 3.64/0.99      | v2_struct_0(X2_49)
% 3.64/0.99      | v2_struct_0(sK2)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(sK2)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(sK2)
% 3.64/0.99      | ~ v1_funct_1(X1_50)
% 3.64/0.99      | ~ v1_funct_1(X0_50) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_279]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7108,plain,
% 3.64/0.99      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
% 3.64/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3))
% 3.64/0.99      | ~ v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 3.64/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 3.64/0.99      | ~ m1_pre_topc(sK4,sK1)
% 3.64/0.99      | ~ m1_pre_topc(sK3,sK4)
% 3.64/0.99      | ~ m1_pre_topc(sK3,sK1)
% 3.64/0.99      | ~ m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 3.64/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.64/0.99      | v2_struct_0(sK4)
% 3.64/0.99      | v2_struct_0(sK1)
% 3.64/0.99      | v2_struct_0(sK2)
% 3.64/0.99      | v2_struct_0(sK3)
% 3.64/0.99      | ~ v2_pre_topc(sK1)
% 3.64/0.99      | ~ v2_pre_topc(sK2)
% 3.64/0.99      | ~ l1_pre_topc(sK1)
% 3.64/0.99      | ~ l1_pre_topc(sK2)
% 3.64/0.99      | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4))
% 3.64/0.99      | ~ v1_funct_1(sK5) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_1229]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_15,negated_conjecture,
% 3.64/0.99      ( m1_pre_topc(sK4,sK1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_273,negated_conjecture,
% 3.64/0.99      ( m1_pre_topc(sK4,sK1) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_748,plain,
% 3.64/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_12,negated_conjecture,
% 3.64/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.64/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_276,negated_conjecture,
% 3.64/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_745,plain,
% 3.64/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_4,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.64/0.99      | ~ m1_pre_topc(X3,X4)
% 3.64/0.99      | ~ m1_pre_topc(X3,X1)
% 3.64/0.99      | ~ m1_pre_topc(X1,X4)
% 3.64/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.64/0.99      | v2_struct_0(X4)
% 3.64/0.99      | v2_struct_0(X2)
% 3.64/0.99      | ~ v2_pre_topc(X2)
% 3.64/0.99      | ~ v2_pre_topc(X4)
% 3.64/0.99      | ~ l1_pre_topc(X2)
% 3.64/0.99      | ~ l1_pre_topc(X4)
% 3.64/0.99      | ~ v1_funct_1(X0)
% 3.64/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_284,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X2_49)
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X2_49)
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X0_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.64/0.99      | v2_struct_0(X2_49)
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X2_49)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(X2_49)
% 3.64/0.99      | ~ v1_funct_1(X0_50)
% 3.64/0.99      | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X3_49)) = k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_737,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k3_tmap_1(X3_49,X1_49,X0_49,X2_49,X0_50)
% 3.64/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X2_49,X0_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X3_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X2_49,X3_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X3_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X3_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X3_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2487,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)
% 3.64/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_745,c_737]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_21,negated_conjecture,
% 3.64/0.99      ( ~ v2_struct_0(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_28,plain,
% 3.64/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_20,negated_conjecture,
% 3.64/0.99      ( v2_pre_topc(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_29,plain,
% 3.64/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_19,negated_conjecture,
% 3.64/0.99      ( l1_pre_topc(sK2) ),
% 3.64/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_30,plain,
% 3.64/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_14,negated_conjecture,
% 3.64/0.99      ( v1_funct_1(sK5) ),
% 3.64/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_35,plain,
% 3.64/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_13,negated_conjecture,
% 3.64/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_36,plain,
% 3.64/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2644,plain,
% 3.64/0.99      ( v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)
% 3.64/0.99      | m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_2487,c_28,c_29,c_30,c_35,c_36,c_37,c_1103]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2645,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)
% 3.64/0.99      | m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top ),
% 3.64/0.99      inference(renaming,[status(thm)],[c_2644]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2658,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK1,sK2,sK1,sK4,sK5)
% 3.64/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_748,c_2645]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.64/0.99      | ~ m1_pre_topc(X3,X1)
% 3.64/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.64/0.99      | v2_struct_0(X1)
% 3.64/0.99      | v2_struct_0(X2)
% 3.64/0.99      | ~ v2_pre_topc(X2)
% 3.64/0.99      | ~ v2_pre_topc(X1)
% 3.64/0.99      | ~ l1_pre_topc(X2)
% 3.64/0.99      | ~ l1_pre_topc(X1)
% 3.64/0.99      | ~ v1_funct_1(X0)
% 3.64/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.64/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_285,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ m1_pre_topc(X2_49,X0_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | v2_struct_0(X0_49)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X0_49)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(X0_49)
% 3.64/0.99      | ~ v1_funct_1(X0_50)
% 3.64/0.99      | k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k2_tmap_1(X0_49,X1_49,X0_50,X2_49) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_736,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_50,u1_struct_0(X2_49)) = k2_tmap_1(X0_49,X1_49,X0_50,X2_49)
% 3.64/0.99      | v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X2_49,X0_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X0_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X0_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X0_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1677,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k2_tmap_1(sK1,sK2,sK5,X0_49)
% 3.64/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,sK1) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_745,c_736]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_24,negated_conjecture,
% 3.64/0.99      ( ~ v2_struct_0(sK1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_25,plain,
% 3.64/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_23,negated_conjecture,
% 3.64/0.99      ( v2_pre_topc(sK1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_26,plain,
% 3.64/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_22,negated_conjecture,
% 3.64/0.99      ( l1_pre_topc(sK1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_27,plain,
% 3.64/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2124,plain,
% 3.64/0.99      ( m1_pre_topc(X0_49,sK1) != iProver_top
% 3.64/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k2_tmap_1(sK1,sK2,sK5,X0_49) ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_1677,c_25,c_26,c_27,c_28,c_29,c_30,c_35,c_36]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2125,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_49)) = k2_tmap_1(sK1,sK2,sK5,X0_49)
% 3.64/0.99      | m1_pre_topc(X0_49,sK1) != iProver_top ),
% 3.64/0.99      inference(renaming,[status(thm)],[c_2124]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2132,plain,
% 3.64/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK1,sK2,sK5,sK4) ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_748,c_2125]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2692,plain,
% 3.64/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK4,sK5) = k2_tmap_1(sK1,sK2,sK5,sK4)
% 3.64/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.64/0.99      inference(light_normalisation,[status(thm)],[c_2658,c_2132]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_34,plain,
% 3.64/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_8,plain,
% 3.64/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_43,plain,
% 3.64/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.64/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_45,plain,
% 3.64/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3276,plain,
% 3.64/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK4,sK5) = k2_tmap_1(sK1,sK2,sK5,sK4) ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_2692,c_25,c_26,c_27,c_34,c_45]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_5,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.64/0.99      | ~ m1_pre_topc(X3,X4)
% 3.64/0.99      | ~ m1_pre_topc(X1,X4)
% 3.64/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.64/0.99      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.64/0.99      | v2_struct_0(X4)
% 3.64/0.99      | v2_struct_0(X2)
% 3.64/0.99      | ~ v2_pre_topc(X2)
% 3.64/0.99      | ~ v2_pre_topc(X4)
% 3.64/0.99      | ~ l1_pre_topc(X2)
% 3.64/0.99      | ~ l1_pre_topc(X4)
% 3.64/0.99      | ~ v1_funct_1(X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_283,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X2_49)
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X2_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.64/0.99      | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49))))
% 3.64/0.99      | v2_struct_0(X2_49)
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X2_49)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(X2_49)
% 3.64/0.99      | ~ v1_funct_1(X0_50) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_738,plain,
% 3.64/0.99      ( v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X2_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X3_49,X2_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | m1_subset_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49)))) = iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X2_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_0,plain,
% 3.64/0.99      ( r2_funct_2(X0,X1,X2,X3)
% 3.64/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.64/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.64/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.64/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.64/0.99      | ~ v1_funct_1(X3)
% 3.64/0.99      | ~ v1_funct_1(X2)
% 3.64/0.99      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_288,plain,
% 3.64/0.99      ( r2_funct_2(X0_51,X1_51,X0_50,X1_50)
% 3.64/0.99      | ~ v1_funct_2(X1_50,X0_51,X1_51)
% 3.64/0.99      | ~ v1_funct_2(X0_50,X0_51,X1_51)
% 3.64/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.64/0.99      | ~ v1_funct_1(X1_50)
% 3.64/0.99      | ~ v1_funct_1(X0_50)
% 3.64/0.99      | k1_funct_1(X1_50,sK0(X0_51,X0_50,X1_50)) != k1_funct_1(X0_50,sK0(X0_51,X0_50,X1_50)) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_733,plain,
% 3.64/0.99      ( k1_funct_1(X0_50,sK0(X0_51,X1_50,X0_50)) != k1_funct_1(X1_50,sK0(X0_51,X1_50,X0_50))
% 3.64/0.99      | r2_funct_2(X0_51,X1_51,X1_50,X0_50) = iProver_top
% 3.64/0.99      | v1_funct_2(X1_50,X0_51,X1_51) != iProver_top
% 3.64/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.64/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.64/0.99      | v1_funct_1(X1_50) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1220,plain,
% 3.64/0.99      ( r2_funct_2(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 3.64/0.99      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(equality_resolution,[status(thm)],[c_733]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1796,plain,
% 3.64/0.99      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50)) = iProver_top
% 3.64/0.99      | v1_funct_2(X0_50,u1_struct_0(X3_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | v1_funct_2(k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50),u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X3_49,X2_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X2_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X2_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50)) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_738,c_1220]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_7,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.64/0.99      | ~ m1_pre_topc(X3,X4)
% 3.64/0.99      | ~ m1_pre_topc(X1,X4)
% 3.64/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.64/0.99      | v2_struct_0(X4)
% 3.64/0.99      | v2_struct_0(X2)
% 3.64/0.99      | ~ v2_pre_topc(X2)
% 3.64/0.99      | ~ v2_pre_topc(X4)
% 3.64/0.99      | ~ l1_pre_topc(X2)
% 3.64/0.99      | ~ l1_pre_topc(X4)
% 3.64/0.99      | ~ v1_funct_1(X0)
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_281,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X2_49)
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X2_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.64/0.99      | v2_struct_0(X2_49)
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X2_49)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(X2_49)
% 3.64/0.99      | ~ v1_funct_1(X0_50)
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50)) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_740,plain,
% 3.64/0.99      ( v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X2_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X3_49,X2_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X2_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50)) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_6,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.64/0.99      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.64/0.99      | ~ m1_pre_topc(X4,X3)
% 3.64/0.99      | ~ m1_pre_topc(X1,X3)
% 3.64/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.64/0.99      | v2_struct_0(X3)
% 3.64/0.99      | v2_struct_0(X2)
% 3.64/0.99      | ~ v2_pre_topc(X2)
% 3.64/0.99      | ~ v2_pre_topc(X3)
% 3.64/0.99      | ~ l1_pre_topc(X2)
% 3.64/0.99      | ~ l1_pre_topc(X3)
% 3.64/0.99      | ~ v1_funct_1(X0) ),
% 3.64/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_282,plain,
% 3.64/0.99      ( ~ v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 3.64/0.99      | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),u1_struct_0(X3_49),u1_struct_0(X1_49))
% 3.64/0.99      | ~ m1_pre_topc(X3_49,X2_49)
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X2_49)
% 3.64/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | v2_struct_0(X2_49)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(X2_49)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(X2_49)
% 3.64/0.99      | ~ v1_funct_1(X0_50) ),
% 3.64/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_739,plain,
% 3.64/0.99      ( v1_funct_2(X0_50,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | v1_funct_2(k3_tmap_1(X2_49,X1_49,X0_49,X3_49,X0_50),u1_struct_0(X3_49),u1_struct_0(X1_49)) = iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X2_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X3_49,X2_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X2_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2835,plain,
% 3.64/0.99      ( r2_funct_2(u1_struct_0(X0_49),u1_struct_0(X1_49),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50),k3_tmap_1(X2_49,X1_49,X3_49,X0_49,X0_50)) = iProver_top
% 3.64/0.99      | v1_funct_2(X0_50,u1_struct_0(X3_49),u1_struct_0(X1_49)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X2_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X3_49,X2_49) != iProver_top
% 3.64/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_49),u1_struct_0(X1_49)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(X2_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X2_49) != iProver_top
% 3.64/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 3.64/0.99      inference(forward_subsumption_resolution,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_1796,c_740,c_739]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3282,plain,
% 3.64/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4)) = iProver_top
% 3.64/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.64/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3276,c_2835]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3371,plain,
% 3.64/0.99      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK4),k2_tmap_1(sK1,sK2,sK5,sK4))
% 3.64/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 3.64/0.99      | ~ m1_pre_topc(sK4,sK1)
% 3.64/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.64/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.64/0.99      | v2_struct_0(sK1)
% 3.64/0.99      | v2_struct_0(sK2)
% 3.64/0.99      | ~ v2_pre_topc(sK1)
% 3.64/0.99      | ~ v2_pre_topc(sK2)
% 3.64/0.99      | ~ l1_pre_topc(sK1)
% 3.64/0.99      | ~ l1_pre_topc(sK2)
% 3.64/0.99      | ~ v1_funct_1(sK5) ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3282]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1694,plain,
% 3.64/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_745,c_740]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_37,plain,
% 3.64/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1068,plain,
% 3.64/0.99      ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 3.64/0.99      | ~ m1_pre_topc(X0_49,X1_49)
% 3.64/0.99      | ~ m1_pre_topc(sK1,X1_49)
% 3.64/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.64/0.99      | v2_struct_0(X1_49)
% 3.64/0.99      | v2_struct_0(sK2)
% 3.64/0.99      | ~ v2_pre_topc(X1_49)
% 3.64/0.99      | ~ v2_pre_topc(sK2)
% 3.64/0.99      | ~ l1_pre_topc(X1_49)
% 3.64/0.99      | ~ l1_pre_topc(sK2)
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5))
% 3.64/0.99      | ~ v1_funct_1(sK5) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_281]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_1069,plain,
% 3.64/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2317,plain,
% 3.64/0.99      ( v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top ),
% 3.64/0.99      inference(global_propositional_subsumption,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_1694,c_28,c_29,c_30,c_35,c_36]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_2318,plain,
% 3.64/0.99      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,X1_49) != iProver_top
% 3.64/0.99      | v2_struct_0(X1_49) = iProver_top
% 3.64/0.99      | v2_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | l1_pre_topc(X1_49) != iProver_top
% 3.64/0.99      | v1_funct_1(k3_tmap_1(X1_49,sK2,sK1,X0_49,sK5)) = iProver_top ),
% 3.64/0.99      inference(renaming,[status(thm)],[c_2317]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3281,plain,
% 3.64/0.99      ( m1_pre_topc(sK4,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.64/0.99      | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) = iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3276,c_2318]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3370,plain,
% 3.64/0.99      ( ~ m1_pre_topc(sK4,sK1)
% 3.64/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.64/0.99      | v2_struct_0(sK1)
% 3.64/0.99      | ~ v2_pre_topc(sK1)
% 3.64/0.99      | ~ l1_pre_topc(sK1)
% 3.64/0.99      | v1_funct_1(k2_tmap_1(sK1,sK2,sK5,sK4)) ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3281]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3280,plain,
% 3.64/0.99      ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top
% 3.64/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.64/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3276,c_739]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3369,plain,
% 3.64/0.99      ( v1_funct_2(k2_tmap_1(sK1,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
% 3.64/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 3.64/0.99      | ~ m1_pre_topc(sK4,sK1)
% 3.64/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.64/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.64/0.99      | v2_struct_0(sK1)
% 3.64/0.99      | v2_struct_0(sK2)
% 3.64/0.99      | ~ v2_pre_topc(sK1)
% 3.64/0.99      | ~ v2_pre_topc(sK2)
% 3.64/0.99      | ~ l1_pre_topc(sK1)
% 3.64/0.99      | ~ l1_pre_topc(sK2)
% 3.64/0.99      | ~ v1_funct_1(sK5) ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3280]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3279,plain,
% 3.64/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK4,sK1) != iProver_top
% 3.64/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.64/0.99      | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top
% 3.64/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.64/0.99      | v2_struct_0(sK1) = iProver_top
% 3.64/0.99      | v2_struct_0(sK2) = iProver_top
% 3.64/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.64/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.64/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.64/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.64/0.99      inference(superposition,[status(thm)],[c_3276,c_738]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_3368,plain,
% 3.64/0.99      ( ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 3.64/0.99      | ~ m1_pre_topc(sK4,sK1)
% 3.64/0.99      | ~ m1_pre_topc(sK1,sK1)
% 3.64/0.99      | m1_subset_1(k2_tmap_1(sK1,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 3.64/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.64/0.99      | v2_struct_0(sK1)
% 3.64/0.99      | v2_struct_0(sK2)
% 3.64/0.99      | ~ v2_pre_topc(sK1)
% 3.64/0.99      | ~ v2_pre_topc(sK2)
% 3.64/0.99      | ~ l1_pre_topc(sK1)
% 3.64/0.99      | ~ l1_pre_topc(sK2)
% 3.64/0.99      | ~ v1_funct_1(sK5) ),
% 3.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3279]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_44,plain,
% 3.64/0.99      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 3.64/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_10,negated_conjecture,
% 3.64/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,k2_tmap_1(sK1,sK2,sK5,sK4)),k2_tmap_1(sK1,sK2,sK5,sK3)) ),
% 3.64/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_11,negated_conjecture,
% 3.64/0.99      ( m1_pre_topc(sK3,sK4) ),
% 3.64/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_16,negated_conjecture,
% 3.64/0.99      ( ~ v2_struct_0(sK4) ),
% 3.64/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_17,negated_conjecture,
% 3.64/0.99      ( m1_pre_topc(sK3,sK1) ),
% 3.64/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(c_18,negated_conjecture,
% 3.64/0.99      ( ~ v2_struct_0(sK3) ),
% 3.64/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.64/0.99  
% 3.64/0.99  cnf(contradiction,plain,
% 3.64/0.99      ( $false ),
% 3.64/0.99      inference(minisat,
% 3.64/0.99                [status(thm)],
% 3.64/0.99                [c_7108,c_3371,c_3370,c_3369,c_3368,c_44,c_10,c_11,c_12,
% 3.64/0.99                 c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,
% 3.64/0.99                 c_24]) ).
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.99  
% 3.64/0.99  ------                               Statistics
% 3.64/0.99  
% 3.64/0.99  ------ General
% 3.64/0.99  
% 3.64/0.99  abstr_ref_over_cycles:                  0
% 3.64/0.99  abstr_ref_under_cycles:                 0
% 3.64/0.99  gc_basic_clause_elim:                   0
% 3.64/0.99  forced_gc_time:                         0
% 3.64/0.99  parsing_time:                           0.014
% 3.64/0.99  unif_index_cands_time:                  0.
% 3.64/0.99  unif_index_add_time:                    0.
% 3.64/0.99  orderings_time:                         0.
% 3.64/0.99  out_proof_time:                         0.013
% 3.64/0.99  total_time:                             0.311
% 3.64/0.99  num_of_symbols:                         54
% 3.64/0.99  num_of_terms:                           6088
% 3.64/0.99  
% 3.64/0.99  ------ Preprocessing
% 3.64/0.99  
% 3.64/0.99  num_of_splits:                          0
% 3.64/0.99  num_of_split_atoms:                     0
% 3.64/0.99  num_of_reused_defs:                     0
% 3.64/0.99  num_eq_ax_congr_red:                    34
% 3.64/0.99  num_of_sem_filtered_clauses:            1
% 3.64/0.99  num_of_subtypes:                        5
% 3.64/0.99  monotx_restored_types:                  0
% 3.64/0.99  sat_num_of_epr_types:                   0
% 3.64/0.99  sat_num_of_non_cyclic_types:            0
% 3.64/0.99  sat_guarded_non_collapsed_types:        0
% 3.64/0.99  num_pure_diseq_elim:                    0
% 3.64/0.99  simp_replaced_by:                       0
% 3.64/0.99  res_preprocessed:                       98
% 3.64/0.99  prep_upred:                             0
% 3.64/0.99  prep_unflattend:                        0
% 3.64/0.99  smt_new_axioms:                         0
% 3.64/0.99  pred_elim_cands:                        8
% 3.64/0.99  pred_elim:                              0
% 3.64/0.99  pred_elim_cl:                           0
% 3.64/0.99  pred_elim_cycles:                       1
% 3.64/0.99  merged_defs:                            0
% 3.64/0.99  merged_defs_ncl:                        0
% 3.64/0.99  bin_hyper_res:                          0
% 3.64/0.99  prep_cycles:                            3
% 3.64/0.99  pred_elim_time:                         0.
% 3.64/0.99  splitting_time:                         0.
% 3.64/0.99  sem_filter_time:                        0.
% 3.64/0.99  monotx_time:                            0.
% 3.64/0.99  subtype_inf_time:                       0.
% 3.64/0.99  
% 3.64/0.99  ------ Problem properties
% 3.64/0.99  
% 3.64/0.99  clauses:                                25
% 3.64/0.99  conjectures:                            15
% 3.64/0.99  epr:                                    13
% 3.64/0.99  horn:                                   18
% 3.64/0.99  ground:                                 15
% 3.64/0.99  unary:                                  15
% 3.64/0.99  binary:                                 1
% 3.64/0.99  lits:                                   121
% 3.64/0.99  lits_eq:                                4
% 3.64/0.99  fd_pure:                                0
% 3.64/0.99  fd_pseudo:                              0
% 3.64/0.99  fd_cond:                                0
% 3.64/0.99  fd_pseudo_cond:                         0
% 3.64/0.99  ac_symbols:                             0
% 3.64/0.99  
% 3.64/0.99  ------ Propositional Solver
% 3.64/0.99  
% 3.64/0.99  prop_solver_calls:                      25
% 3.64/0.99  prop_fast_solver_calls:                 1760
% 3.64/0.99  smt_solver_calls:                       0
% 3.64/0.99  smt_fast_solver_calls:                  0
% 3.64/0.99  prop_num_of_clauses:                    1639
% 3.64/0.99  prop_preprocess_simplified:             4860
% 3.64/0.99  prop_fo_subsumed:                       267
% 3.64/0.99  prop_solver_time:                       0.
% 3.64/0.99  smt_solver_time:                        0.
% 3.64/0.99  smt_fast_solver_time:                   0.
% 3.64/0.99  prop_fast_solver_time:                  0.
% 3.64/0.99  prop_unsat_core_time:                   0.
% 3.64/0.99  
% 3.64/0.99  ------ QBF
% 3.64/0.99  
% 3.64/0.99  qbf_q_res:                              0
% 3.64/0.99  qbf_num_tautologies:                    0
% 3.64/0.99  qbf_prep_cycles:                        0
% 3.64/0.99  
% 3.64/0.99  ------ BMC1
% 3.64/0.99  
% 3.64/0.99  bmc1_current_bound:                     -1
% 3.64/0.99  bmc1_last_solved_bound:                 -1
% 3.64/0.99  bmc1_unsat_core_size:                   -1
% 3.64/0.99  bmc1_unsat_core_parents_size:           -1
% 3.64/0.99  bmc1_merge_next_fun:                    0
% 3.64/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.64/0.99  
% 3.64/0.99  ------ Instantiation
% 3.64/0.99  
% 3.64/0.99  inst_num_of_clauses:                    637
% 3.64/0.99  inst_num_in_passive:                    236
% 3.64/0.99  inst_num_in_active:                     334
% 3.64/0.99  inst_num_in_unprocessed:                66
% 3.64/0.99  inst_num_of_loops:                      412
% 3.64/0.99  inst_num_of_learning_restarts:          0
% 3.64/0.99  inst_num_moves_active_passive:          69
% 3.64/0.99  inst_lit_activity:                      0
% 3.64/0.99  inst_lit_activity_moves:                0
% 3.64/0.99  inst_num_tautologies:                   0
% 3.64/0.99  inst_num_prop_implied:                  0
% 3.64/0.99  inst_num_existing_simplified:           0
% 3.64/0.99  inst_num_eq_res_simplified:             0
% 3.64/0.99  inst_num_child_elim:                    0
% 3.64/0.99  inst_num_of_dismatching_blockings:      508
% 3.64/0.99  inst_num_of_non_proper_insts:           975
% 3.64/0.99  inst_num_of_duplicates:                 0
% 3.64/0.99  inst_inst_num_from_inst_to_res:         0
% 3.64/0.99  inst_dismatching_checking_time:         0.
% 3.64/0.99  
% 3.64/0.99  ------ Resolution
% 3.64/0.99  
% 3.64/0.99  res_num_of_clauses:                     0
% 3.64/0.99  res_num_in_passive:                     0
% 3.64/0.99  res_num_in_active:                      0
% 3.64/0.99  res_num_of_loops:                       101
% 3.64/0.99  res_forward_subset_subsumed:            175
% 3.64/0.99  res_backward_subset_subsumed:           0
% 3.64/0.99  res_forward_subsumed:                   0
% 3.64/0.99  res_backward_subsumed:                  0
% 3.64/0.99  res_forward_subsumption_resolution:     0
% 3.64/0.99  res_backward_subsumption_resolution:    0
% 3.64/0.99  res_clause_to_clause_subsumption:       554
% 3.64/0.99  res_orphan_elimination:                 0
% 3.64/0.99  res_tautology_del:                      139
% 3.64/0.99  res_num_eq_res_simplified:              0
% 3.64/0.99  res_num_sel_changes:                    0
% 3.64/0.99  res_moves_from_active_to_pass:          0
% 3.64/0.99  
% 3.64/0.99  ------ Superposition
% 3.64/0.99  
% 3.64/0.99  sup_time_total:                         0.
% 3.64/0.99  sup_time_generating:                    0.
% 3.64/0.99  sup_time_sim_full:                      0.
% 3.64/0.99  sup_time_sim_immed:                     0.
% 3.64/0.99  
% 3.64/0.99  sup_num_of_clauses:                     107
% 3.64/0.99  sup_num_in_active:                      82
% 3.64/0.99  sup_num_in_passive:                     25
% 3.64/0.99  sup_num_of_loops:                       82
% 3.64/0.99  sup_fw_superposition:                   45
% 3.64/0.99  sup_bw_superposition:                   47
% 3.64/0.99  sup_immediate_simplified:               22
% 3.64/0.99  sup_given_eliminated:                   0
% 3.64/0.99  comparisons_done:                       0
% 3.64/0.99  comparisons_avoided:                    0
% 3.64/0.99  
% 3.64/0.99  ------ Simplifications
% 3.64/0.99  
% 3.64/0.99  
% 3.64/0.99  sim_fw_subset_subsumed:                 1
% 3.64/0.99  sim_bw_subset_subsumed:                 2
% 3.64/0.99  sim_fw_subsumed:                        2
% 3.64/0.99  sim_bw_subsumed:                        0
% 3.64/0.99  sim_fw_subsumption_res:                 6
% 3.64/0.99  sim_bw_subsumption_res:                 2
% 3.64/0.99  sim_tautology_del:                      0
% 3.64/0.99  sim_eq_tautology_del:                   2
% 3.64/0.99  sim_eq_res_simp:                        0
% 3.64/0.99  sim_fw_demodulated:                     0
% 3.64/0.99  sim_bw_demodulated:                     0
% 3.64/0.99  sim_light_normalised:                   17
% 3.64/0.99  sim_joinable_taut:                      0
% 3.64/0.99  sim_joinable_simp:                      0
% 3.64/0.99  sim_ac_normalised:                      0
% 3.64/0.99  sim_smt_subsumption:                    0
% 3.64/0.99  
%------------------------------------------------------------------------------
